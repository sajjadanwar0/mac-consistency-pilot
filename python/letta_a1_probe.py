#!/usr/bin/env python3
"""
letta_a1_probe.py
=================
Significance probe for the consistency-lattice paper.

QUESTION
    Does A1 (stale-generation) fire in a REAL agent-memory system --- Letta
    (formerly MemGPT) --- under a NATURAL multi-writer workload, without
    engineering the susceptible shared-mutable-cell pattern by hand?

WHY THIS IS THE LEVER
    The paper's ceiling is external validity: A1 fires 0/600 on real MAST
    traces, the susceptible pattern is one production frameworks design
    around, and the single in-the-wild instance (deer-flow #3123) is an L0
    lost-update --- an A1 *cousin*, not A1 proper. A single NON-ENGINEERED A1
    firing in a real agent-memory system converts that concession from "L0
    cousin" to "A1 in the wild," which is the 6 -> 7 -> 8 move.

    The workload is deliberately NOT a worst-case topology. The shared memory
    block is Letta's own first-class collaboration primitive, and the
    susceptible pattern is the vendor's documented default: the Letta docs
    warn that "multiple agents doing memory_replace on the same block
    simultaneously leads to lost updates" and recommend "design blocks so
    each agent updates their own section." That recommended avoidance IS the
    ad-hoc discipline the demarcation thesis names. We run the UNGUARDED
    default (one shared block, no per-agent sections) and let the LLM
    decisions be unconstrained; only the scheduling is realistic concurrency.

WHAT IS AND IS NOT FABRICATED
    read_value is the actual shared-block contents the agents saw before the
    concurrent round. write_value is recovered from the agent's OWN memory
    tool-call arguments (what it told core_memory_append/replace to write) ---
    not a post-hoc block snapshot, which under concurrency captures other
    agents' racing writes and is therefore contamination-prone. The 'committed'
    flag is ground truth from the final block (did this agent's marker
    survive). Nothing is synthesized; if a turn made no tool call, write_value
    falls back to the read value and the run warns.

AUTHORITATIVE DETECTOR
    The reference screen here is a CONVENIENCE signal. Any witness you intend
    to report MUST be certified by the verified Rust detector (verus-detector
    A1), fed the emitted OpRecords exactly as the MAST 0/600 traces were fed.

REQUIRES (user side --- LLMs are not run by the paper tooling author)
    pip install letta-client
    export LETTA_API_KEY=...            # Letta Cloud; or --base-url for self-host
    A model provider configured in Letta. Use a tool-reliable model:
    gpt-4o-mini frequently answers in chat WITHOUT calling memory tools, which
    yields an empty (all-seed) trace. Prefer --model openai/gpt-4o or a Claude
    model. The calibration pass below detects a non-writing model up front.

USAGE
    python letta_a1_probe.py --agents 3 --rounds 4 --model openai/gpt-4o \
        --edit-mode replace --out letta_a1_trace.json
    # then CERTIFY any witness with the verified detector:
    #   run verus-detector A1 over letta_a1_trace.json (same loader as MAST)

Method names track the letta-client SDK current as of 2026-06; if your
installed version differs, only the calls in LettaProbe.* need adjusting.
"""

import argparse
import atexit
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field, asdict


@dataclass
class OpRecord:
    op_id: int
    agent: str
    cell: str
    t_read: int
    t_commit: int
    read_values: dict = field(default_factory=dict)
    write_values: dict = field(default_factory=dict)
    committed: bool = True


def _to_jsonable(o):
    """Best-effort convert an SDK object (pydantic model, etc.) to plain
    dicts/lists so we can walk it without knowing attribute names."""
    if hasattr(o, "model_dump"):
        try:
            return o.model_dump()
        except Exception:
            pass
    if hasattr(o, "dict") and callable(getattr(o, "dict")):
        try:
            return o.dict()
        except Exception:
            pass
    if isinstance(o, dict):
        return {k: _to_jsonable(v) for k, v in o.items()}
    if isinstance(o, (list, tuple)):
        return [_to_jsonable(v) for v in o]
    if hasattr(o, "__dict__"):
        try:
            return {k: _to_jsonable(v) for k, v in vars(o).items()}
        except Exception:
            return str(o)
    return o


def _iter_tool_calls(obj):
    """Yield (name, arguments) for every nested dict that carries both ---
    catches tool calls regardless of how the SDK nests them."""
    if isinstance(obj, dict):
        name = obj.get("name")
        args = obj.get("arguments")
        if name is not None and args is not None:
            yield name, args
        for v in obj.values():
            yield from _iter_tool_calls(v)
    elif isinstance(obj, (list, tuple)):
        for v in obj:
            yield from _iter_tool_calls(v)


class LettaProbe:
    def __init__(self, model, edit_mode, base_url=None, token=None, block_limit=8000):
        try:
            from letta_client import Letta
        except ImportError:
            sys.exit("letta-client not installed. Run: pip install letta-client")
        kwargs = {}
        if token:
            kwargs["token"] = token
        if base_url:
            kwargs["base_url"] = base_url
        self.client = Letta(**kwargs)
        self.model = model
        self.edit_mode = edit_mode
        self.block_limit = block_limit
        self.cell = "shared_plan"
        self.block_id = None
        self.agents = []

    def create_shared_block(self, seed):
        blk = self.client.blocks.create(
            label=self.cell, value=seed, limit=self.block_limit,
            description=("The team's shared plan. ALL agents read and edit "
                         "THIS block (label 'shared_plan') with their memory "
                         "tools. It is the single shared workspace."),
        )
        self.block_id = blk.id
        return blk.id

    def create_agents(self, n):
        for i in range(n):
            a = self.client.agents.create(
                name=f"a1probe_agent_{i+1}",
                model=self.model,
                block_ids=[self.block_id],
                include_base_tools=True,
                memory_blocks=[{"label": "persona",
                                "value": f"You are teammate {i+1}."}],
            )
            self.agents.append((f"agent_{i+1}", a.id))
        return self.agents

    def cleanup(self):
        """Delete the agents and shared block this run created, so repeated
        runs stay within the account's agent cap."""
        for _, aid in self.agents:
            try:
                self.client.agents.delete(aid)
            except Exception:
                pass
        if self.block_id:
            try:
                self.client.blocks.delete(self.block_id)
            except Exception:
                pass

    def read_block(self):
        blk = self.client.blocks.retrieve(self.block_id)
        return blk.value if getattr(blk, "value", None) is not None else ""

    def marker(self, name, round_no):
        return f"[{name}|r{round_no}]"

    def run_turn(self, name, agent_id, round_no, current, mode=None):
        """Drive one agent turn. Returns nothing; the agent edits the block."""
        mode = mode or self.edit_mode
        mk = self.marker(name, round_no)
        if mode == "replace":
            how = (f"Call your core_memory_replace tool on the block named "
                   f"'shared_plan'. Replace its ENTIRE current contents with "
                   f"those same contents plus exactly one new final line that "
                   f"begins with the marker '{mk} ' followed by your single "
                   f"concrete next step. Preserve every existing line.")
        else:
            how = (f"Call your core_memory_append tool on the block named "
                   f"'shared_plan'. Append exactly one new line that begins "
                   f"with the marker '{mk} ' followed by your single concrete "
                   f"next step.")
        msg = (
            "The team's shared plan (block label 'shared_plan') currently "
            f"reads, between the markers:\n---BEGIN---\n{current}\n---END---\n"
            f"{how}\nMake exactly one memory-tool call. Do not reply in chat."
        )
        return self.client.agents.messages.create(
            agent_id=agent_id,
            messages=[{"role": "user", "content": msg}],
        )

    def extract_write(self, response, pre, mode, mk):
        """Recover what THIS agent actually committed, from its memory
        tool-call arguments in the response --- contamination-proof, unlike a
        post-hoc snapshot of the shared block under concurrency. Walks the
        whole JSON-ified response so it is robust to SDK attribute naming.
        Falls back to pre if no memory tool call is found."""
        import json as _json
        content = None
        for name, args in _iter_tool_calls(_to_jsonable(response)):
            if "memory" not in str(name).lower():
                continue
            if isinstance(args, str):
                try:
                    args = _json.loads(args)
                except Exception:
                    args = {}
            if not isinstance(args, dict):
                continue
            for key in ("new_string", "content", "new_content", "new_str",
                        "value", "text"):
                if args.get(key):
                    content = args[key]
                    break
            if content:
                break
        if content is None:
            return pre
        if mode == "replace":
            return content if mk in content else (pre.rstrip() + "\n" + content)
        return pre.rstrip() + "\n" + content

    def calibrate(self):
        """One isolated turn per agent; confirm each can actually write the
        shared block. Returns the set of write-capable agent names."""
        capable = set()
        for name, aid in self.agents:
            before = self.read_block()
            self.run_turn(name, aid, "cal", before, mode="append")
            after = self.read_block()
            if self.marker(name, "cal") in after or after != before:
                capable.add(name)
        return capable


def run_concurrent_round(probe, agents, round_no, clock):
    """All agents read the same pre-state, then commit in a real race.
    Each agent's write_value is the ACTUAL block snapshot taken right after
    its own turn returns (not synthesized)."""
    pre = probe.read_block()
    t_read = next(clock)

    def worker(name, aid):
        resp = probe.run_turn(name, aid, round_no, pre)
        write_val = probe.extract_write(resp, pre, probe.edit_mode,
                                        probe.marker(name, round_no))
        return name, write_val, time.monotonic()

    done = []
    with ThreadPoolExecutor(max_workers=len(agents)) as ex:
        futs = [ex.submit(worker, name, aid) for name, aid in agents]
        for f in as_completed(futs):
            done.append(f.result())

    done.sort(key=lambda x: x[2])
    post_final = probe.read_block()
    records = []
    for name, write_val, _ in done:
        t_commit = next(clock)
        mk = probe.marker(name, round_no)
        records.append(OpRecord(
            op_id=-1, agent=name, cell=probe.cell,
            t_read=t_read, t_commit=t_commit,
            read_values={probe.cell: pre},
            write_values={probe.cell: write_val},
            committed=(mk in post_final),
        ))
    return records, pre, post_final


def _lines(s):
    return [ln.strip() for ln in (s or "").splitlines() if ln.strip()]


def a1_screen(records):
    """Convenience A1 screen (NOT authoritative). A turn k is an A1 witness if
    another agent committed between k's read and k's commit (so k could not
    have seen it) AND the line(s) that commit added are absent from both k's
    read and k's observed write (k's stale generation clobbered it)."""
    cell_turns = {}
    for rec in records:
        cell_turns.setdefault(rec.cell, []).append(rec)
    witnesses, stale_only = [], []
    for cell, turns in cell_turns.items():
        turns = sorted(turns, key=lambda x: (x.t_commit, x.t_read))
        for k in turns:
            intervening = [t for t in turns
                           if t.agent != k.agent
                           and t.t_commit > k.t_read
                           and t.t_commit < k.t_commit]
            if not intervening:
                continue
            r_k = _lines(k.read_values.get(cell, ""))
            w_k = _lines(k.write_values.get(cell, ""))
            found = False
            for iv in intervening:
                before_iv = [t for t in turns if t.t_commit < iv.t_commit]
                base = before_iv[-1].write_values.get(cell, "") if before_iv else ""
                added = [ln for ln in _lines(iv.write_values.get(cell, ""))
                         if ln not in _lines(base)]
                unseen = [ln for ln in added if ln not in r_k]
                lost = [ln for ln in unseen if ln not in w_k]
                if added and lost:
                    witnesses.append({
                        "cell": cell, "stale_reader": k.agent,
                        "stale_read_op": k.op_id, "lost_writer": iv.agent,
                        "lost_write_op": iv.op_id, "lost_lines": lost})
                    found = True
                    break
            if not found:
                stale_only.append((cell, k.agent, k.op_id))
    return witnesses, stale_only


def main():
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--agents", type=int, default=3)
    ap.add_argument("--rounds", type=int, default=4)
    ap.add_argument("--model", default="openai/gpt-4o")
    ap.add_argument("--edit-mode", choices=["replace", "append"],
                    default="append",
                    help="append = reliable write that can still lose updates "
                         "under the race (recommended); replace = aggressive "
                         "read-modify-write, but frequently no-ops when the "
                         "match string is stale")
    ap.add_argument("--base-url", default=None,
                    help="self-hosted server URL, e.g. http://localhost:8283 "
                         "(omit for Letta Cloud)")
    ap.add_argument("--token", default=None,
                    help="server password/token if your self-hosted server "
                         "sets one (omit for an unauthenticated local server)")
    ap.add_argument("--out", default="letta_a1_trace.json")
    ap.add_argument("--seed-plan", default="Shared plan:\n")
    ap.add_argument("--reset", action="store_true",
                    help="delete leftover a1probe_* agents before running")
    ap.add_argument("--purge-all", action="store_true",
                    help="delete ALL agents in the account and exit (use this "
                         "to recover from the 3-agent free-tier cap)")
    ap.add_argument("--dump-response", action="store_true",
                    help="send ONE turn, dump the raw response structure to "
                         "letta_response_debug.json, and exit (use if the "
                         "'no per-agent write captured' warning fires)")
    args = ap.parse_args()

    def clockgen():
        t = 0
        while True:
            t += 1
            yield t
    clock = clockgen()

    print(f"[probe] agents={args.agents} rounds={args.rounds} "
          f"model={args.model} edit-mode={args.edit_mode}", file=sys.stderr)
    probe = LettaProbe(model=args.model, edit_mode=args.edit_mode,
                       base_url=args.base_url, token=args.token)

    if args.purge_all:
        n = 0
        for a in probe.client.agents.list():
            try:
                probe.client.agents.delete(a.id)
                n += 1
            except Exception:
                pass
        print(f"[probe] purged {n} agents; rerun without --purge-all to probe.")
        return

    if args.reset:
        n = 0
        for a in probe.client.agents.list():
            if str(getattr(a, "name", "")).startswith("a1probe_"):
                try:
                    probe.client.agents.delete(a.id)
                    n += 1
                except Exception:
                    pass
        print(f"[probe] reset: deleted {n} leftover a1probe_* agents",
              file=sys.stderr)

    probe.create_shared_block(seed=args.seed_plan)
    atexit.register(probe.cleanup)

    if args.dump_response:
        probe.create_agents(1)
        name, aid = probe.agents[0]
        resp = probe.run_turn(name, aid, "dbg", args.seed_plan, mode="append")
        with open("letta_response_debug.json", "w") as f:
            json.dump(_to_jsonable(resp), f, indent=2, default=str)
        print("[probe] dumped raw response -> letta_response_debug.json "
              "(send me this file)", file=sys.stderr)
        return

    agents = probe.create_agents(args.agents)
    print(f"[probe] shared block {probe.block_id} -> {len(agents)} agents",
          file=sys.stderr)

    capable = probe.calibrate()
    print(f"[probe] write-capable agents: {sorted(capable)} "
          f"({len(capable)}/{len(agents)})", file=sys.stderr)
    if not capable:
        sys.exit(
            "\nABORT: no agent edited the shared block during calibration.\n"
            "This is a WIRING null, not a result. Likely causes: the model is\n"
            "not calling core_memory tools (try --model openai/gpt-4o or a\n"
            "Claude model), base tools are disabled, or the block label does\n"
            "not match. Do NOT report this as 'no A1'.")

    try:
        probe.client.blocks.update(probe.block_id, value=args.seed_plan)
    except Exception:
        try:
            probe.client.blocks.update(block_id=probe.block_id, value=args.seed_plan)
        except Exception:
            pass

    records = []
    op_id = 0
    rounds_with_writes = 0
    for r in range(args.rounds):
        recs, pre, post = run_concurrent_round(probe, agents, r, clock)
        wrote = any(rec.committed for rec in recs) or post != pre
        rounds_with_writes += 1 if wrote else 0
        for rec in recs:
            rec.op_id = op_id
            op_id += 1
            records.append(rec)

    captured = sum(1 for r in records
                   if r.write_values[probe.cell] != r.read_values[probe.cell])
    if captured == 0:
        print("\nWARNING: no per-agent write captured from tool-call arguments "
              "(write == read for every turn). Your letta_client response "
              "shape may differ; the emitted trace is NOT valid for the "
              "verified detector. Print one response's .messages and adjust "
              "extract_write() accordingly.", file=sys.stderr)

    with open(args.out, "w") as f:
        json.dump([asdict(r) for r in records], f, indent=2)
    print(f"[probe] wrote {len(records)} OpRecords -> {args.out}",
          file=sys.stderr)

    lost = [r for r in records if not r.committed]
    witnesses, stale_only = a1_screen(records)
    print("\n==== concurrency screen (NOT authoritative) ====")
    print(f"rounds in which the block changed:           {rounds_with_writes}/{args.rounds}")
    print(f"LOST-UPDATE (L0) writes [marker gone from final block]: {len(lost)}/{len(records)}")
    print(f"clobber events [later concurrent write overwrote an earlier one]: {len(witnesses)}")
    for w in witnesses:
        print(f"  - L0 on '{w['cell']}': {w['stale_reader']} (op "
              f"{w['stale_read_op']}) overwrote {w['lost_writer']}'s committed "
              f"write (op {w['lost_write_op']}); lost: {w['lost_lines']}")

    print("\n---- CLASSIFICATION ----")
    if rounds_with_writes == 0:
        print("WIRING NULL: agents wrote during calibration but not during the "
              "rounds. Inspect the block manually; do not report as 'no anomaly'.")
    elif lost:
        print("This is a LOST-UPDATE anomaly (L0) -- the same class as "
              "deer-flow #3123. It is NOT certified A1 (Def. stale-generation):\n"
              "  * read-times here are completion-order tie-breaks, not measured;\n"
              "  * more fundamentally, Letta re-injects the CURRENT block into\n"
              "    each agent's context at generation time, so this black-box\n"
              "    run cannot establish that any agent GENERATED from a stale\n"
              "    value -- which Def. A1 requires. Asserting A1 from this trace\n"
              "    would be manufacturing the result.\n"
              "Report it as a second real-system L0 instance (corroborating the\n"
              "demarcation thesis), NOT as A1 in the wild. Certifying genuine A1\n"
              "would require white-box capture of the value each agent's\n"
              "generation actually consumed.")
    else:
        print("No lost update observed: agents wrote concurrently but the store "
              "serialized all edits. This CORROBORATES the demarcation thesis "
              "(even a contention-prone real system stayed consistent here).")


if __name__ == "__main__":
    main()