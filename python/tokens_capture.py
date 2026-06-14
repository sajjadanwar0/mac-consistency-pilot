"""
tokens_capture.py
=================

Drop-in instrumentation that replaces the post-hoc
character-derived cost estimate of paper_v4_6 §5.5 (Table 6) with
measured per-call token counts from gpt-4o `usage` callbacks.

Design
------
The pilot harness calls into AutoGen, which calls the OpenAI
client. The OpenAI Python SDK returns a `usage` object on every
ChatCompletion response containing `prompt_tokens`,
`completion_tokens`, and `total_tokens`. We capture every such
response, attribute its tokens to the currently-active agent
session and OpRecord, and emit a sidecar JSONL file aligned 1:1
with the existing trace JSONL.

Three integration points are supported (use whichever fits your
pilot harness):

  1. `AutoGenUsageCollector`      — drop-in replacement for an
     AutoGen-style ChatCompletionContext that records usage
     after every model call. Wrap your existing client.

  2. `wrap_openai_client(client)` — monkey-patches an
     `openai.OpenAI` (or `AsyncOpenAI`) instance so that every
     `chat.completions.create` call routes through a wrapper
     that captures `usage`. No AutoGen dependency.

  3. `SessionRecorder`            — a pure context manager that
     accumulates usage records under a session_id and writes a
     JSONL file at session end. Use this directly when wiring
     into a non-AutoGen harness.

Output schema
-------------
One JSONL file per session, one line per model call:

    {
      "session_id":        "edit-review-pessimistic-007",
      "runtime":           "pessimistic",
      "workload":          "edit-review",
      "agent_id":          "editor",
      "op_index":          3,                 # OpRecord index within session
      "call_index":        2,                 # call index within OpRecord
      "model":             "gpt-4o-2024-08-06",
      "prompt_tokens":     1247,
      "completion_tokens": 84,
      "total_tokens":      1331,
      "input_cost_usd":    0.003117,
      "output_cost_usd":   0.000840,
      "total_cost_usd":    0.003957,
      "wall_clock_ms":     2931,
      "timestamp_iso":     "2026-05-10T17:42:11.428Z"
    }

Aggregation across sessions to produce Table 6 is performed by
`aggregate_runs(...)`; see `__main__` for an example.

Pricing
-------
Pricing is configurable. Defaults are gpt-4o pricing as of
2026-05-10:

    input  : $2.50 per million tokens
    output : $10.00 per million tokens

Override via `Pricing.from_env()` (reads
`MAC_OPENAI_INPUT_PRICE_PER_M` and
`MAC_OPENAI_OUTPUT_PRICE_PER_M`) or by passing a custom
`Pricing(...)` instance.

Reproducibility
---------------
This module captures all data needed to reconstruct the
cost-of-prevention table from raw token counts at a future
pricing snapshot. The token counts themselves are
pricing-independent.
"""

from __future__ import annotations

import contextlib
import datetime as _dt
import json
import os
import statistics
import threading
import time
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Any, Callable, Iterable, Iterator, Optional



@dataclass(frozen=True)
class Pricing:
    """Per-million-token USD pricing for input and output."""
    input_per_m_usd: float
    output_per_m_usd: float
    label: str = "gpt-4o-2024-08-06"

    @classmethod
    def gpt_4o_default(cls) -> "Pricing":
        return cls(input_per_m_usd=2.50, output_per_m_usd=10.00)

    @classmethod
    def from_env(cls) -> "Pricing":
        return cls(
            input_per_m_usd=float(
                os.environ.get("MAC_OPENAI_INPUT_PRICE_PER_M", "2.50")
            ),
            output_per_m_usd=float(
                os.environ.get("MAC_OPENAI_OUTPUT_PRICE_PER_M", "10.00")
            ),
            label=os.environ.get("MAC_OPENAI_PRICING_LABEL", "gpt-4o"),
        )

    def cost_usd(self, prompt_tokens: int, completion_tokens: int) -> tuple[float, float, float]:
        """Return (input_cost, output_cost, total_cost) in USD."""
        inp = prompt_tokens * self.input_per_m_usd / 1_000_000.0
        out = completion_tokens * self.output_per_m_usd / 1_000_000.0
        return (inp, out, inp + out)



@dataclass
class CallRecord:
    """Single model call with measured usage."""
    session_id: str
    runtime: str
    workload: str
    agent_id: str
    op_index: int
    call_index: int
    model: str
    prompt_tokens: int
    completion_tokens: int
    total_tokens: int
    input_cost_usd: float
    output_cost_usd: float
    total_cost_usd: float
    wall_clock_ms: int
    timestamp_iso: str

    def to_json_line(self) -> str:
        return json.dumps(asdict(self), separators=(",", ":"))



class SessionRecorder:
    """
    Thread-safe accumulator for one pilot session. Use as a context
    manager:

        with SessionRecorder(out_dir, session_id, runtime, workload,
                             pricing=Pricing.gpt_4o_default()) as rec:
            rec.bind_agent("editor")
            rec.bind_op_index(0)
            ... agent does work, calls model ...
            rec.record_call(model="gpt-4o-2024-08-06",
                            prompt_tokens=1247,
                            completion_tokens=84,
                            wall_clock_ms=2931)
            rec.bind_op_index(1)
            rec.record_call(...)

    On exit the recorder writes
    `{out_dir}/{session_id}.tokens.jsonl`.
    """

    def __init__(
            self,
            out_dir: Path | str,
            session_id: str,
            runtime: str,
            workload: str,
            *,
            pricing: Pricing | None = None,
    ) -> None:
        self.out_dir = Path(out_dir)
        self.session_id = session_id
        self.runtime = runtime
        self.workload = workload
        self.pricing = pricing or Pricing.gpt_4o_default()
        self._records: list[CallRecord] = []
        self._lock = threading.Lock()
        self._agent_id = ""
        self._op_index = 0
        self._call_counter_per_op: dict[tuple[str, int], int] = {}


    def __enter__(self) -> "SessionRecorder":
        self.out_dir.mkdir(parents=True, exist_ok=True)
        return self

    def __exit__(self, exc_type, exc, tb) -> None:
        self.flush()


    def bind_agent(self, agent_id: str) -> None:
        with self._lock:
            self._agent_id = agent_id

    def bind_op_index(self, op_index: int) -> None:
        with self._lock:
            self._op_index = op_index


    def record_call(
            self,
            *,
            model: str,
            prompt_tokens: int,
            completion_tokens: int,
            wall_clock_ms: int,
            agent_id: Optional[str] = None,
            op_index: Optional[int] = None,
    ) -> CallRecord:
        """Append one model call. Returns the record."""
        with self._lock:
            aid = agent_id if agent_id is not None else self._agent_id
            oi = op_index if op_index is not None else self._op_index
            key = (aid, oi)
            ci = self._call_counter_per_op.get(key, 0)
            self._call_counter_per_op[key] = ci + 1

        inp, out, tot = self.pricing.cost_usd(prompt_tokens, completion_tokens)
        rec = CallRecord(
            session_id=self.session_id,
            runtime=self.runtime,
            workload=self.workload,
            agent_id=aid,
            op_index=oi,
            call_index=ci,
            model=model,
            prompt_tokens=prompt_tokens,
            completion_tokens=completion_tokens,
            total_tokens=prompt_tokens + completion_tokens,
            input_cost_usd=inp,
            output_cost_usd=out,
            total_cost_usd=tot,
            wall_clock_ms=wall_clock_ms,
            timestamp_iso=_dt.datetime.now(_dt.timezone.utc)
            .isoformat(timespec="milliseconds")
            .replace("+00:00", "Z"),
            )
        with self._lock:
            self._records.append(rec)
        return rec

    def record_response(
            self,
            response: Any,
            *,
            wall_clock_ms: int,
            agent_id: Optional[str] = None,
            op_index: Optional[int] = None,
    ) -> Optional[CallRecord]:
        """
        Convenience: extract usage from an OpenAI-shaped response
        and record it. Returns None if the response has no usage
        attribute (e.g. streaming response that wasn't aggregated).
        """
        usage = getattr(response, "usage", None)
        if usage is None:
            return None
        prompt_tokens = getattr(usage, "prompt_tokens", None)
        completion_tokens = getattr(usage, "completion_tokens", None)
        if prompt_tokens is None or completion_tokens is None:
            return None
        model = getattr(response, "model", self.pricing.label)
        return self.record_call(
            model=model,
            prompt_tokens=int(prompt_tokens),
            completion_tokens=int(completion_tokens),
            wall_clock_ms=wall_clock_ms,
            agent_id=agent_id,
            op_index=op_index,
        )


    def flush(self) -> Path:
        out = self.out_dir / f"{self.session_id}.tokens.jsonl"
        with self._lock:
            records = list(self._records)
        with out.open("w", encoding="utf-8") as f:
            for rec in records:
                f.write(rec.to_json_line())
                f.write("\n")
        return out


    def session_summary(self) -> dict[str, Any]:
        """Summary stats for the session; used by aggregate_runs."""
        with self._lock:
            records = list(self._records)
        if not records:
            return {
                "session_id": self.session_id,
                "runtime": self.runtime,
                "workload": self.workload,
                "n_calls": 0,
                "prompt_tokens": 0,
                "completion_tokens": 0,
                "total_tokens": 0,
                "total_cost_usd": 0.0,
                "wall_clock_ms": 0,
            }
        return {
            "session_id": self.session_id,
            "runtime": self.runtime,
            "workload": self.workload,
            "n_calls": len(records),
            "prompt_tokens": sum(r.prompt_tokens for r in records),
            "completion_tokens": sum(r.completion_tokens for r in records),
            "total_tokens": sum(r.total_tokens for r in records),
            "total_cost_usd": sum(r.total_cost_usd for r in records),
            "wall_clock_ms": sum(r.wall_clock_ms for r in records),
        }



def wrap_openai_client(
        client: Any,
        recorder: SessionRecorder,
) -> Any:
    """
    Monkey-patch an `openai.OpenAI` (or `AsyncOpenAI`) client so
    that every `client.chat.completions.create(...)` call captures
    its usage into `recorder`.

    Usage:

        from openai import OpenAI
        client = OpenAI()
        wrap_openai_client(client, recorder)
        # now every chat.completions.create call records usage
    """
    chat = getattr(client, "chat", None)
    completions = getattr(chat, "completions", None) if chat is not None else None
    if completions is None or not hasattr(completions, "create"):
        raise TypeError(
            "wrap_openai_client expects an openai.OpenAI-shaped client "
            "with .chat.completions.create"
        )

    original_create = completions.create
    is_async = "Async" in type(client).__name__

    if is_async:
        async def patched_create(*args: Any, **kwargs: Any) -> Any:
            t0 = time.monotonic()
            response = await original_create(*args, **kwargs)
            elapsed_ms = int((time.monotonic() - t0) * 1000)
            recorder.record_response(response, wall_clock_ms=elapsed_ms)
            return response
        completions.create = patched_create
    else:
        def patched_create(*args: Any, **kwargs: Any) -> Any:
            t0 = time.monotonic()
            response = original_create(*args, **kwargs)
            elapsed_ms = int((time.monotonic() - t0) * 1000)
            recorder.record_response(response, wall_clock_ms=elapsed_ms)
            return response
        completions.create = patched_create

    return client



class AutoGenUsageCollector:
    """
    Wraps an AutoGen-compatible OpenAIChatCompletionClient to
    capture usage. AutoGen exposes responses with a `.usage`
    attribute on the message stream.

    AutoGen's APIs have changed over versions; this class exposes
    a permissive interface: pass any object with a `.create(...)`
    method that returns an awaitable-or-sync response with
    `.usage` and we'll capture from it.

        from autogen_ext.models.openai import OpenAIChatCompletionClient
        client = OpenAIChatCompletionClient(model="gpt-4o")
        wrapped = AutoGenUsageCollector(client, recorder)
        # now use `wrapped` wherever you'd use `client`
    """

    def __init__(self, inner: Any, recorder: SessionRecorder) -> None:
        self._inner = inner
        self._recorder = recorder

    def __getattr__(self, name: str) -> Any:
        return getattr(self._inner, name)

    async def create(self, *args: Any, **kwargs: Any) -> Any:
        t0 = time.monotonic()
        result = self._inner.create(*args, **kwargs)
        if hasattr(result, "__await__"):
            response = await result
        else:
            response = result
        elapsed_ms = int((time.monotonic() - t0) * 1000)
        self._recorder.record_response(response, wall_clock_ms=elapsed_ms)
        return response



def _bootstrap_ci(
        samples: list[float],
        *,
        n_resamples: int = 1000,
        confidence: float = 0.95,
        rng_seed: int = 0,
) -> tuple[float, float]:
    """
    Percentile bootstrap CI on the mean of `samples`. Returns
    (lower, upper). Uses a fixed seed for reproducibility; pass
    rng_seed=None to use system entropy if desired.
    """
    if not samples:
        return (0.0, 0.0)
    import random
    rng = random.Random(rng_seed)
    n = len(samples)
    means: list[float] = []
    for _ in range(n_resamples):
        resample = [samples[rng.randrange(n)] for _ in range(n)]
        means.append(statistics.fmean(resample))
    means.sort()
    alpha = (1.0 - confidence) / 2.0
    lo_idx = max(0, int(alpha * n_resamples))
    hi_idx = min(n_resamples - 1, int((1.0 - alpha) * n_resamples) - 1)
    return (means[lo_idx], means[hi_idx])


def aggregate_runs(
        sessions_dir: Path | str,
        *,
        runtimes: Iterable[str] = ("vanilla", "pessimistic", "snapshot_isolation"),
        workloads: Iterable[str] = ("edit-review", "plan-execute", "triage"),
        n_resamples: int = 1000,
        pricing: Pricing | None = None,
) -> dict[str, Any]:
    """
    Read all `*.tokens.jsonl` files under `sessions_dir`, group by
    (runtime, workload), and produce the cost-of-prevention table
    with bootstrap 95% CIs.

    Returns:
        {
          "pricing": {...},
          "cells": [
            {
              "runtime": "vanilla",
              "workload": "edit-review",
              "n_sessions": 100,
              "mean_cost_usd": 0.00206,
              "ci_low_usd":   0.00198,
              "ci_high_usd":  0.00214,
              "mean_prompt_tokens": 583.4,
              "mean_completion_tokens": 79.1,
              "mean_total_tokens": 662.5,
              "median_wall_clock_ms": 2918,
            },
            ...
          ]
        }
    """
    pricing = pricing or Pricing.gpt_4o_default()
    sessions_dir = Path(sessions_dir)

    by_cell: dict[tuple[str, str], list[dict[str, float]]] = {}
    for path in sorted(sessions_dir.glob("*.tokens.jsonl")):
        per_session_total = {
            "prompt": 0,
            "completion": 0,
            "total": 0,
            "cost_usd": 0.0,
            "wall_ms": 0,
        }
        runtime: str = ""
        workload: str = ""
        with path.open("r", encoding="utf-8") as f:
            for line in f:
                if not line.strip():
                    continue
                rec = json.loads(line)
                runtime = rec.get("runtime", runtime)
                workload = rec.get("workload", workload)
                per_session_total["prompt"] += int(rec.get("prompt_tokens", 0))
                per_session_total["completion"] += int(rec.get("completion_tokens", 0))
                per_session_total["total"] += int(rec.get("total_tokens", 0))
                per_session_total["cost_usd"] += float(rec.get("total_cost_usd", 0.0))
                per_session_total["wall_ms"] += int(rec.get("wall_clock_ms", 0))
        if not runtime or not workload:
            continue
        if runtime in runtimes and workload in workloads:
            by_cell.setdefault((runtime, workload), []).append(per_session_total)

    cells: list[dict[str, Any]] = []
    for runtime in runtimes:
        for workload in workloads:
            sessions = by_cell.get((runtime, workload), [])
            n = len(sessions)
            costs = [s["cost_usd"] for s in sessions]
            prompts = [s["prompt"] for s in sessions]
            comps = [s["completion"] for s in sessions]
            tots = [s["total"] for s in sessions]
            walls = [s["wall_ms"] for s in sessions]
            ci_lo, ci_hi = _bootstrap_ci(costs, n_resamples=n_resamples)
            cells.append({
                "runtime": runtime,
                "workload": workload,
                "n_sessions": n,
                "mean_cost_usd": statistics.fmean(costs) if costs else 0.0,
                "ci_low_usd": ci_lo,
                "ci_high_usd": ci_hi,
                "mean_prompt_tokens": statistics.fmean(prompts) if prompts else 0.0,
                "mean_completion_tokens": statistics.fmean(comps) if comps else 0.0,
                "mean_total_tokens": statistics.fmean(tots) if tots else 0.0,
                "median_wall_clock_ms": statistics.median(walls) if walls else 0,
            })

    return {
        "pricing": asdict(pricing),
        "cells": cells,
    }


def emit_latex_table(
        aggregate: dict[str, Any],
        *,
        runtimes: Iterable[str] = ("vanilla", "pessimistic", "snapshot_isolation"),
        workloads: Iterable[str] = ("edit-review", "plan-execute", "triage"),
        label: str = "tab:cost-measured",
        caption: Optional[str] = None,
) -> str:
    """
    Render the aggregate as the LaTeX block expected by §5.5
    (paper_v4_7 BLOCK 5, Option A). Returns a full table
    environment as a string.
    """
    pricing = aggregate["pricing"]
    if caption is None:
        caption = (
            f"Per-session token cost by runtime and workload, captured from "
            f"\\texttt{{usage}} callbacks. Pricing: "
            f"\\${pricing['input_per_m_usd']:.2f}/M input, "
            f"\\${pricing['output_per_m_usd']:.2f}/M output. "
            f"95\\,\\% bootstrap CIs on per-session total cost (1{{,}}000 resamples). "
            f"Cost in milli-dollars (m\\$ = USD $\\times 10^{{-3}}$)."
        )

    cell_lookup = {(c["runtime"], c["workload"]): c for c in aggregate["cells"]}

    runtime_label = {
        "vanilla": "Vanilla",
        "pessimistic": "Pessimistic",
        "snapshot_isolation": "Snapshot iso.",
    }

    def fmt_cost(c: dict[str, Any]) -> str:
        m = c["mean_cost_usd"] * 1000.0
        lo = c["ci_low_usd"] * 1000.0
        hi = c["ci_high_usd"] * 1000.0
        return f"\\${m:.2f}\\,m [{lo:.2f}, {hi:.2f}]"

    rows = []
    for r in runtimes:
        cells_in_row = [
            fmt_cost(cell_lookup[(r, w)]) if (r, w) in cell_lookup else "---"
            for w in workloads
        ]
        rows.append(
            f"{runtime_label.get(r, r):<14} & " + " & ".join(cells_in_row) + r" \\"
        )

    header = " & ".join(workloads)
    body = "\n".join(rows)

    return (
        "\\begin{table}[t]\n"
        "\\centering\n"
        f"\\caption{{{caption}}}\n"
        f"\\label{{{label}}}\n"
        "\\small\n"
        "\\begin{tabular}{lccc}\n"
        "\\toprule\n"
        f"Runtime & {header} \\\\\n"
        "\\midrule\n"
        f"{body}\n"
        "\\bottomrule\n"
        "\\end{tabular}\n"
        "\\end{table}\n"
    )



def _cli() -> None:
    import argparse
    p = argparse.ArgumentParser(
        description="Aggregate per-session token JSONL files into a Table 6 LaTeX block."
    )
    p.add_argument(
        "sessions_dir",
        type=Path,
        help="Directory containing *.tokens.jsonl files.",
    )
    p.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Output path for the LaTeX block (default: stdout).",
    )
    p.add_argument(
        "--json",
        action="store_true",
        help="Emit aggregate as JSON instead of LaTeX.",
    )
    p.add_argument("--input-price", type=float, default=None)
    p.add_argument("--output-price", type=float, default=None)
    p.add_argument("--n-resamples", type=int, default=1000)
    args = p.parse_args()

    pricing = Pricing.from_env()
    if args.input_price is not None:
        pricing = Pricing(
            input_per_m_usd=args.input_price,
            output_per_m_usd=args.output_price or pricing.output_per_m_usd,
            label=pricing.label,
        )

    agg = aggregate_runs(
        args.sessions_dir,
        n_resamples=args.n_resamples,
        pricing=pricing,
    )

    if args.json:
        out = json.dumps(agg, indent=2)
    else:
        out = emit_latex_table(agg)

    if args.out is None:
        print(out)
    else:
        args.out.write_text(out, encoding="utf-8")


if __name__ == "__main__":
    _cli()