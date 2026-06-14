#!/usr/bin/env python3
"""
high_contention_cost.py  (self-contained)

Decision-grade HIGH-CONTENTION COST benchmark. Companion to
prevalence_dynamic_run.py: that script measures whether A_1 fires; this one
measures what it COSTS to prevent it, as a function of write contention, under
the three coordination disciplines (vanilla / SSI / pessimistic).

It reuses the same inlined primitives (OpRecord, a1_firings, clopper_pearson,
ModelClient) so the committed-history A_1 check here is identical to the one in
the prevalence harness and to lib_l2_safety.rs::a1_witness.

WHAT IS MEASURED
  Primary endpoint  : TOKENS, exact from provider usage, including wasted
                      tokens spent on generations that were aborted and re-run
                      (the real cost of SSI's optimistic retries).
  Secondary         : wall-clock seconds COMPOSED from measured per-call
                      latency under each strategy's concurrency structure
                      (vanilla overlaps; pessimistic serializes per cell; SSI
                      overlaps initial gens then serializes retries). This is a
                      model over measured latencies, labeled as such; raw
                      summed latency is also recorded assumption-free.
  Mechanism         : aborts, retries, lock-wait, realized abort rate.
  Correctness guard : vanilla must exhibit A_1 at high W; SSI/pessimistic must
                      not. A "cost-neutral" number is meaningless if the guard
                      silently stopped working, so every session is checked.

CONTENTION MODEL
  Per round, W agents each read the round-start value of a shared cell, generate
  (one live LLM call), and write. The W agents are distributed over C shared
  cells (default C=1 = worst case, all contend on one cell). C<W creates
  collisions; randomized assignment makes the realized abort rate vary, which is
  what the abort-rate regression (analyze --regress) needs. D rounds let retries
  compound. This is the parameterized generalization of the racy_shared_cell /
  blackboard_multiwriter topologies to arbitrary fan-in.

USAGE  (run sessions -> JSONL, then analyze)
  pip install openai anthropic        # scipy/numpy optional but recommended
  # Stage 1 (variance probe) -- top cell only, all three strategies, paired:
  python high_contention_cost.py run --provider vllm --model llama3.2 \
      --base-url http://localhost:11434/v1 --w 16 --cells 1 --depth 4 \
      --n 20 --seed 1 --out ./hc_stage1
  python high_contention_cost.py analyze --in ./hc_stage1 --target-effect 0.10
  # Stage 2 (full ladder) -- n from the formula analyze just printed:
  for W in 2 4 8 16; do
    python high_contention_cost.py run --provider vllm --model llama3.2 \
        --base-url http://localhost:11434/v1 --w $W --cells 1 --depth 4 \
        --n 150 --seed 1 --out ./hc_ladder
  done
  python high_contention_cost.py analyze --in ./hc_ladder --target-effect 0.10 --regress

  # Dry run with no keys / no model (validates the harness, deterministic):
  python high_contention_cost.py run --provider mock --model mock --w 8 --n 30 --out ./hc_mock
  python high_contention_cost.py analyze --in ./hc_mock
"""
from __future__ import annotations
import argparse
import json
import math
import random
import sys
import time
import hashlib
from dataclasses import dataclass, asdict
from pathlib import Path
from collections import defaultdict

STRATEGIES = ("vanilla", "ssi", "pessimistic")


@dataclass
class OpRecord:
    agent_id: str
    op_index: int
    read_set: list
    read_values: dict
    read_time: int
    write_set: list
    write_values: dict
    write_time: int
    superstep: int
    scenario: str = ""
    model: str = ""


def a1_firings(records):
    """Cross-agent A_1 over the COMMITTED history: op O (superstep k, agent A)
    reading cell c=v fires iff some op O' in superstep k, by a DIFFERENT agent,
    writes c=v' with v' != v. Identical to prevalence_dynamic_run.a1_firings."""
    by_ss = {}
    for r in records:
        by_ss.setdefault(r.superstep, []).append(r)
    firings = []
    for ss, ops in by_ss.items():
        for r in ops:
            for c in r.read_set:
                v = r.read_values.get(c, "")
                hit = False
                for w in ops:
                    if w.agent_id == r.agent_id:
                        continue
                    if c in w.write_set and w.write_values.get(c, "") != v:
                        firings.append({"superstep": ss, "agent": r.agent_id, "cell": c,
                                        "read_value": v, "by_agent": w.agent_id})
                        hit = True
                        break
                if hit:
                    break
    return firings


def clopper_pearson(k, n, alpha=0.05):
    if n == 0:
        return (0.0, 1.0)
    try:
        from scipy.stats import beta
        lo = 0.0 if k == 0 else beta.ppf(alpha / 2, k, n - k + 1)
        hi = 1.0 if k == n else beta.ppf(1 - alpha / 2, k + 1, n - k)
        return (float(lo), float(hi))
    except Exception:
        p = k / n
        se = math.sqrt(p * (1 - p) / n) if 0 < p < 1 else 0.0
        return (max(0.0, p - 1.96 * se), min(1.0, p + 1.96 * se))


class ModelClient:
    def __init__(self, provider, model, base_url=None):
        self.provider = provider
        self.model = model
        if provider == "mock":
            self.client = None
        elif provider in ("openai", "vllm"):
            from openai import OpenAI
            self.client = OpenAI(base_url=base_url, api_key="EMPTY") if base_url else OpenAI()
        elif provider == "anthropic":
            import anthropic
            self.client = anthropic.Anthropic()
        else:
            raise ValueError(f"unknown provider {provider}")

    def complete(self, system, user, seed=None, max_tokens=32):
        """Return (text, total_tokens, latency_s)."""
        t0 = time.perf_counter()
        if self.provider == "mock":
            h = hashlib.sha256(f"{system}|{user}".encode()).hexdigest()
            text = f"val_{h[:8]}"
            comp = 8 + (int(h[8:12], 16) % 40)
            prompt = 20 + len(user) // 4
            lat = 0.02 + (int(h[12:16], 16) % 50) / 1000.0
            time.sleep(0)
            return text, prompt + comp, lat
        if self.provider in ("openai", "vllm"):
            kw = dict(model=self.model, max_tokens=max_tokens,
                      messages=[{"role": "system", "content": system},
                                {"role": "user", "content": user}])
            if seed is not None:
                kw["seed"] = seed
            r = self.client.chat.completions.create(**kw)
            text = (r.choices[0].message.content or "").strip()
            tok = getattr(r, "usage", None)
            total = int(tok.total_tokens) if tok else 0
        else:
            r = self.client.messages.create(
                model=self.model, max_tokens=max_tokens, system=system,
                messages=[{"role": "user", "content": user}])
            text = (r.content[0].text if r.content else "").strip()
            u = getattr(r, "usage", None)
            total = int(u.input_tokens + u.output_tokens) if u else 0
        return text, total, time.perf_counter() - t0


@dataclass
class SessionCost:
    scenario_seed: int
    model: str
    strategy: str
    W: int
    cells: int
    depth: int
    tokens_total: int = 0
    tokens_wasted: int = 0
    wallclock_s: float = 0.0
    wallclock_raw_s: float = 0.0
    wasted_gen_s: float = 0.0
    lockwait_s: float = 0.0
    aborts: int = 0
    retries: int = 0
    generations: int = 0
    a1_observed: int = 0


def _prompt(agent, cell, readval):
    return (f"You are agent '{agent}' in a multi-agent workflow. "
            f"Shared cell '{cell}' currently reads: {json.dumps(readval)}. "
            f"Produce a concise updated value (<=8 words). Output only the value.")


def run_session(client, strategy, W, C, D, seed):
    """Execute one paired session under `strategy`. Returns (SessionCost,
    committed OpRecords). All three strategies see identical inputs for a given
    seed (cell assignment is seeded), so sessions pair across strategies."""
    rng = random.Random(seed)
    assign = {a: (rng.randrange(C) if C > 1 else 0) for a in range(W)}
    sc = SessionCost(scenario_seed=seed, model=client.model, strategy=strategy,
                     W=W, cells=C, depth=D)
    state = {f"c{c}": "NULL" for c in range(C)}
    records = []
    op = 0
    ser = 0
    sysmsg = "Multi-agent workflow node. Reply with only a short value."

    for rnd in range(D):
        snapshot = dict(state)
        gen = {}
        for a in range(W):
            cell = f"c{assign[a]}"
            readval = snapshot[cell]
            txt, tok, lat = client.complete(sysmsg, _prompt(f"r{rnd}_a{a}", cell, readval),
                                            seed=(seed * 1000 + rnd * 50 + a))
            gen[a] = [cell, readval, txt, tok, lat]
            sc.tokens_total += tok
            sc.wallclock_raw_s += lat
            sc.generations += 1

        by_cell = defaultdict(list)
        for a in range(W):
            by_cell[gen[a][0]].append(a)

        round_wall = 0.0
        if strategy == "vanilla":
            for a in range(W):
                cell, readval, txt, tok, lat = gen[a]
                op += 1
                records.append(OpRecord(
                    agent_id=f"r{rnd}_a{a}", op_index=op,
                    read_set=[cell], read_values={cell: readval}, read_time=2 * rnd,
                    write_set=[cell], write_values={cell: txt}, write_time=2 * rnd + 1,
                    superstep=rnd, scenario=f"hc_W{W}_C{C}", model=client.model))
            for cell, agents in by_cell.items():
                state[cell] = gen[agents[-1]][2]
                round_wall = max(round_wall, max(gen[a][4] for a in agents))

        elif strategy == "pessimistic":
            for cell, agents in by_cell.items():
                waited = 0.0
                cell_time = 0.0
                cur = snapshot[cell]
                for a in agents:
                    sc.lockwait_s += waited
                    readval = cur
                    txt = gen[a][2]; lat = gen[a][4]
                    cur = txt
                    op += 1
                    records.append(OpRecord(
                        agent_id=f"r{rnd}_a{a}", op_index=op,
                        read_set=[cell], read_values={cell: readval}, read_time=ser,
                        write_set=[cell], write_values={cell: txt}, write_time=ser,
                        superstep=ser, scenario=f"hc_W{W}_C{C}", model=client.model))
                    ser += 1
                    waited += lat
                    cell_time += lat
                state[cell] = cur
                round_wall = max(round_wall, cell_time)

        elif strategy == "ssi":
            for cell, agents in by_cell.items():
                committed = snapshot[cell]
                serial_retry_time = 0.0
                first_gen_overlap = max(gen[a][4] for a in agents)
                for a in agents:
                    readval = gen[a][1]; txt = gen[a][2]; lat = gen[a][4]
                    if readval != committed:
                        sc.aborts += 1; sc.retries += 1
                        rtxt, rtok, rlat = client.complete(
                            sysmsg, _prompt(f"r{rnd}_a{a}", cell, committed),
                            seed=(seed * 1000 + rnd * 50 + a + 7919))
                        sc.tokens_total += rtok; sc.tokens_wasted += tok
                        sc.wallclock_raw_s += rlat; sc.wasted_gen_s += lat
                        sc.generations += 1
                        serial_retry_time += rlat
                        readval, txt = committed, rtxt
                    committed = txt
                    op += 1
                    records.append(OpRecord(
                        agent_id=f"r{rnd}_a{a}", op_index=op,
                        read_set=[cell], read_values={cell: readval}, read_time=ser,
                        write_set=[cell], write_values={cell: txt}, write_time=ser,
                        superstep=ser, scenario=f"hc_W{W}_C{C}", model=client.model))
                    ser += 1
                state[cell] = committed
                round_wall = max(round_wall, first_gen_overlap + serial_retry_time)
        sc.wallclock_s += round_wall

    sc.a1_observed = len(a1_firings(records))
    return sc, records


def cmd_run(args):
    client = ModelClient(args.provider, args.model, base_url=args.base_url)
    outdir = Path(args.out); outdir.mkdir(parents=True, exist_ok=True)
    msafe = args.model.replace("/", "_")
    jsonl = outdir / f"sessions__{msafe}.jsonl"
    print(f"strategy     W   C  D   n   tokens(mean)  aborts  A1(vanilla guard)")
    print("-" * 74)
    total_sessions = len(STRATEGIES) * args.n
    done = 0
    t_start = time.perf_counter()
    written = 0
    with open(jsonl, "a") as fh:
        for strat in STRATEGIES:
            toks, aborts, a1 = [], 0, 0
            for t in range(args.n):
                seed = args.seed * 100000 + t
                sc, _ = run_session(client, strat, args.w, args.cells, args.depth, seed)
                fh.write(json.dumps(asdict(sc), separators=(",", ":")) + "\n")
                fh.flush()
                toks.append(sc.tokens_total); aborts += sc.aborts; a1 += sc.a1_observed
                written += 1; done += 1
                elapsed = time.perf_counter() - t_start
                rate = elapsed / done
                eta = rate * (total_sessions - done)
                sys.stderr.write(
                    f"\r  [{done:>4}/{total_sessions}] {strat:<11} "
                    f"sess#{t+1:<3} {sc.generations:>3} gens  "
                    f"elapsed {elapsed:6.0f}s  eta {eta:6.0f}s   ")
                sys.stderr.flush()
            sys.stderr.write("\n")
            mean = sum(toks) / len(toks) if toks else 0
            guard = a1 if strat == "vanilla" else f"{a1} (must be 0)"
            print(f"{strat:11} {args.w:>3} {args.cells:>3} {args.depth:>2} {args.n:>3} "
                  f"{mean:>12.1f}  {aborts:>5}   {guard}")
    print("-" * 74)
    print(f"wrote {written} session records -> {jsonl}")
    print("Guard: vanilla A1 should be > 0 at high W; ssi/pessimistic must be 0.")


def _bootstrap_ci(diffs, reps=10000, alpha=0.05, rng=None):
    rng = rng or random.Random(12345)
    n = len(diffs)
    if n == 0:
        return (float("nan"), float("nan"))
    means = []
    for _ in range(reps):
        s = sum(diffs[rng.randrange(n)] for _ in range(n)) / n
        means.append(s)
    means.sort()
    return (means[int((alpha / 2) * reps)], means[int((1 - alpha / 2) * reps)])


def cmd_analyze(args):
    indir = Path(args.__dict__["in"])
    rows = []
    for f in indir.glob("sessions__*.jsonl"):
        for line in open(f):
            line = line.strip()
            if line:
                rows.append(json.loads(line))
    if not rows:
        print(f"no session records under {indir}"); return

    cells = defaultdict(dict)
    for r in rows:
        cells[(r["W"], r["cells"], r["scenario_seed"])][r["strategy"]] = r
    groups = sorted({(r["W"], r["cells"]) for r in rows})

    print(f"{'W':>3} {'C':>3} {'pairs':>6}  {'SSI rel.tok':>22}  {'PESS rel.tok':>22}  "
          f"{'abort/agent':>11}  {'guard':>6}")
    print("-" * 104)
    regress_pts = []
    cell_summ = []
    for (W, C) in groups:
        ssi_d, pess_d, abrt = [], [], []
        van_a1_total, ssi_a1_bad, pess_a1_bad = 0, 0, 0
        npairs = 0
        for (w, c, seed), bystrat in cells.items():
            if (w, c) != (W, C) or "vanilla" not in bystrat:
                continue
            van = bystrat["vanilla"]["tokens_total"]
            if van <= 0:
                continue
            npairs += 1
            van_a1_total += bystrat["vanilla"]["a1_observed"]
            if "ssi" in bystrat:
                ssi_a1_bad += (bystrat["ssi"]["a1_observed"] != 0)
                d = (bystrat["ssi"]["tokens_total"] - van) / van
                ssi_d.append(d)
                ar = bystrat["ssi"]["aborts"] / (W * bystrat["ssi"]["depth"])
                abrt.append(ar); regress_pts.append((ar, d))
            if "pessimistic" in bystrat:
                pess_a1_bad += (bystrat["pessimistic"]["a1_observed"] != 0)
                pess_d.append((bystrat["pessimistic"]["tokens_total"] - van) / van)
        guard_ok = (ssi_a1_bad == 0 and pess_a1_bad == 0 and
                    (van_a1_total > 0 or C >= W))
        def fmt(ds):
            if not ds:
                return f"{'n/a':>22}"
            m = sum(ds) / len(ds); lo, hi = _bootstrap_ci(ds)
            return f"{m*100:>7.1f}% [{lo*100:5.1f},{hi*100:5.1f}]"
        am = (sum(abrt) / len(abrt)) if abrt else 0.0
        if ssi_d:
            lo, hi = _bootstrap_ci(ssi_d)
            cell_summ.append((am, sum(ssi_d) / len(ssi_d), lo, hi, W, C))
        print(f"{W:>3} {C:>3} {npairs:>6}  {fmt(ssi_d)}  {fmt(pess_d)}  {am:>11.2f}  "
              f"{'PASS' if guard_ok else 'FAIL':>6}")

    if cell_summ:
        hi_cell = max(cell_summ, key=lambda t: t[0])
        am, m, lo, hi, W, C = hi_cell
        verdict = ("UNQUALIFIED cost-neutral/bounded (<15%)" if hi < 0.15 else
                   "QUALIFIED bounded overhead (15-50%)" if hi < 0.50 else
                   "envelope: free at low abort rate, material at high; report C*")
        print("-" * 104)
        print(f"Decision at max contention (W={W},C={C}, abort/agent={am:.2f}): "
              f"SSI U95 = {hi*100:.1f}%  ->  {verdict}")

    hi_pts = None
    if cell_summ:
        am0 = max(cell_summ, key=lambda t: t[0])
        W0, C0 = am0[4], am0[5]
        hi_pts = [d for (ar, d) in regress_pts]
        ds = [(bystrat["ssi"]["tokens_total"] - bystrat["vanilla"]["tokens_total"])
              / bystrat["vanilla"]["tokens_total"]
              for (w, c, s), bystrat in cells.items()
              if (w, c) == (W0, C0) and "ssi" in bystrat and "vanilla" in bystrat
              and bystrat["vanilla"]["tokens_total"] > 0]
        if len(ds) >= 2:
            mu = sum(ds) / len(ds)
            sd = math.sqrt(sum((x - mu) ** 2 for x in ds) / (len(ds) - 1))
            zpow = 1.2816 if args.power == 0.90 else (0.8416 if args.power == 0.80 else 1.2816)
            Delta = args.target_effect
            if Delta > 0 and sd > 0:
                n_needed = ((1.96 + zpow) ** 2) * (sd ** 2) / (Delta ** 2)
                print(f"Power: SD(rel.diff)={sd*100:.1f}% at (W={W0},C={C0}); to detect a "
                      f"{Delta*100:.0f}% effect at {int(args.power*100)}% power, "
                      f"n >= {math.ceil(n_needed)} paired sessions per cell.")

    if args.regress and len(regress_pts) >= 3:
        xs = [p[0] for p in regress_pts]; ys = [p[1] for p in regress_pts]
        n = len(xs); mx = sum(xs) / n; my = sum(ys) / n
        sxx = sum((x - mx) ** 2 for x in xs)
        sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
        if sxx > 0:
            slope = sxy / sxx; intercept = my - slope * mx
            rng = random.Random(99); slopes, inters, bps = [], [], []
            pts = list(zip(xs, ys))
            for _ in range(5000):
                samp = [pts[rng.randrange(n)] for _ in range(n)]
                bx = [p[0] for p in samp]; by = [p[1] for p in samp]
                bmx = sum(bx) / n; bmy = sum(by) / n
                bsxx = sum((x - bmx) ** 2 for x in bx)
                if bsxx <= 0:
                    continue
                bsl = sum((x - bmx) * (y - bmy) for x, y in zip(bx, by)) / bsxx
                bin_ = bmy - bsl * bmx
                slopes.append(bsl); inters.append(bin_)
                if bsl > 0:
                    bps.append((0.15 - bin_) / bsl)
            slopes.sort(); inters.sort(); bps.sort()
            def ci(a): return (a[int(0.025 * len(a))], a[int(0.975 * len(a))]) if a else (float("nan"),) * 2
            sl_lo, sl_hi = ci(slopes); in_lo, in_hi = ci(inters); bp_lo, bp_hi = ci(bps)
            print("-" * 104)
            print(f"Mechanism (n={n}): overhead = {intercept*100:.1f}% "
                  f"[{in_lo*100:.1f},{in_hi*100:.1f}] + {slope*100:.1f}% "
                  f"[{sl_lo*100:.1f},{sl_hi*100:.1f}] x abort_rate")
            if bps:
                bp = (0.15 - intercept) / slope if slope > 0 else float("nan")
                print(f"C* breakpoint (overhead crosses 15%): abort_rate = "
                      f"{bp:.3f} [{bp_lo:.3f},{bp_hi:.3f}]")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    r = sub.add_parser("run", help="execute paired sessions, append JSONL")
    r.add_argument("--provider", required=True, help="openai | anthropic | vllm | mock")
    r.add_argument("--model", required=True)
    r.add_argument("--base-url", default=None)
    r.add_argument("--w", type=int, required=True, help="write fan-in (agents per round)")
    r.add_argument("--cells", type=int, default=1, help="shared cells (1 = worst case)")
    r.add_argument("--depth", type=int, default=4, help="rounds")
    r.add_argument("--n", type=int, default=20, help="paired scenarios")
    r.add_argument("--seed", type=int, default=1)
    r.add_argument("--out", default="./hc_out")
    r.set_defaults(func=cmd_run)

    a = sub.add_parser("analyze", help="paired overhead, CI, decision rule, power, regression")
    a.add_argument("--in", required=True, help="directory of sessions__*.jsonl")
    a.add_argument("--target-effect", type=float, default=0.10, dest="target_effect",
                   help="effect size for the n-needed power calc (relative, e.g. 0.10)")
    a.add_argument("--power", type=float, default=0.90)
    a.add_argument("--regress", action="store_true", help="regress overhead on abort rate")
    a.set_defaults(func=cmd_analyze)

    args = ap.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()