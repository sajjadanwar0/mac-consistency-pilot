#!/usr/bin/env python3
"""langgraph_static.py -- a STATIC front end for LangGraph graphs.

WHY (2026-09-19 round 35). Section 5.8's structural susceptibility bound ran on
sixteen topologies TRANSCRIBED from published descriptions, and
langgraph_extract.py showed why it could not run on a compiled graph: LangGraph
reports a node's read set as the whole state schema and exposes no per-node
write set. The information is in the SOURCE: a node function's
`state["k"]` / `state.get("k")` / `state.k` accesses are its reads, the keys of
the dict it returns are its writes, and `add_edge` calls with a common source
are a fork whose successors run in one superstep. This file recovers exactly
that from a Python file's AST, with no import and no execution of the analysed
code, so it can be pointed at third-party repositories.

OVERRULED (rounds <= 34): reading structural susceptibility off declared
topologies.

WHAT IT DECIDES, per StateGraph construction site:
  co-scheduled pairs   nodes that one fork releases into the same superstep
                       (siblings, and equal depths along unconditional chains),
                       plus the targets of a router or Command that returns a
                       list;
  per pair             rw keys  -- a key one node reads and the other writes --
                       split by channel: PLAIN (last value wins: the reader's
                       basis is overwritten at the same barrier, the shape of
                       Section 5.13's superstep experiment), REDUCER (the basis
                       is extended, the usual parallel-agents-on-`messages`
                       idiom), or an UNKNOWN channel (schema not in the file);
  per graph            rw_plain > rw_unknown_channel > unknown >
                       rw_reducer_only > parallel_clean > sequential.

WHAT IT REFUSES TO GUESS. A node whose function is not a def or lambda in the
same file, a state object used other than by constant key, a return that is
not a dict literal (or Command(update={...})): each makes the affected set
UNKNOWN, and a pair with an unknown side and no known rw key is `unknown`, never
`clean`. Unknown graphs are reported as the gap between a lower and an upper
bound, not imputed.

    python3 python/langgraph_static.py FILE.py ...   # JSON facts, one graph per line
    python3 python/langgraph_static.py --selftest    # known-answer fixtures
    python3 python/langgraph_static.py --oracle      # the same fixtures EXECUTED on real
                                                     # LangGraph: static must equal dynamic

The oracle's exit code says WHICH thing happened (2026-09-19 round 36):
    0  every executed fixture agrees with the static analysis
    1  a DISAGREEMENT: the front end is wrong about a fixture
    2  NOT RUN: langgraph cannot be imported by this python3 -- says nothing
       about the front end
    3  a fixture could not be EXECUTED: an environment failure, not a disagreement
Round 35 caught only ImportError. A pydantic / pydantic-core mismatch on AB's
machine raised SystemError deep inside the import, which surfaced as a traceback
here and, in that round's fix script, as the false verdict "the static front end
disagrees with real LangGraph execution". OVERRULED (round 35): one failure code
for three different failures. To get langgraph, use a virtual environment; never
install into an interpreter other tools share.

Standard library only (the oracle needs langgraph). No network.
"""
import ast
import json
import sys

START, END = "__start__", "__end__"
STATE_METHODS = {"get", "keys", "items", "values", "copy", "update", "model_dump", "dict",
                 "setdefault", "pop", "model_copy", "json"}
MAX_DEPTH = 6
STATUS_ORDER = ["rw_plain", "rw_unknown_channel", "unknown", "rw_reducer_only", "parallel_clean", "sequential"]


# ------------------------------------------------------------ node functions
def _own_nodes(fn):
    """Walk a function body without descending into nested defs, lambdas or classes."""
    body = [fn.body] if isinstance(fn, ast.Lambda) else list(fn.body)
    stack = list(body)
    while stack:
        n = stack.pop()
        yield n
        for c in ast.iter_child_nodes(n):
            if not isinstance(c, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)):
                stack.append(c)


def _dict_keys(d):
    """(keys, unknown) of a dict literal / dict(k=v) call."""
    if isinstance(d, ast.Dict):
        keys, unknown = set(), False
        for k in d.keys:
            if isinstance(k, ast.Constant) and isinstance(k.value, str):
                keys.add(k.value)
            else:
                unknown = True          # **spread or computed key
        return keys, unknown
    if isinstance(d, ast.Call) and isinstance(d.func, ast.Name) and d.func.id == "dict" and not d.args:
        return {k.arg for k in d.keywords if k.arg}, any(k.arg is None for k in d.keywords)
    return set(), True


def _const_targets(e):
    """Node names an expression can name: (targets, is_parallel_list, dynamic), where
    dynamic is False, "send" (a Send fan-out) or "unresolved" (not a constant)."""
    if isinstance(e, ast.Constant) and isinstance(e.value, str):
        return [e.value], False, False
    if isinstance(e, ast.Name) and e.id in ("END", "START"):
        return [END if e.id == "END" else START], False, False
    if isinstance(e, (ast.List, ast.Tuple)):
        out, dyn = [], False
        for x in e.elts:
            t, _, d = _const_targets(x)
            out += t
            dyn = "send" if "send" in (dyn, d) else (dyn or d)
        return out, len(e.elts) >= 2, dyn
    if isinstance(e, ast.Call) and getattr(e.func, "id", getattr(e.func, "attr", "")) == "Send":
        t, _, _ = _const_targets(e.args[0]) if e.args else ([], False, False)
        return t, False, "send"
    if isinstance(e, (ast.ListComp, ast.GeneratorExp)):
        t, _, d = _const_targets(e.elt)
        return t, False, d or "unresolved"
    return [], False, "unresolved"


def analyse_fn(fn):
    """Reads and writes of a node function, by constant key, or UNKNOWN."""
    args = [a.arg for a in fn.args.args if a.arg not in ("self", "cls")]
    state = args[0] if args else None
    own = list(_own_nodes(fn))
    parent = {}
    for n in own:
        for c in ast.iter_child_nodes(n):
            parent[id(c)] = n
    reads, reads_unknown = set(), False
    writes, writes_unknown = set(), False
    gotos, goto_parallel, dynamic = [], False, False
    for n in own:
        if isinstance(n, ast.Name) and n.id == state:
            p = parent.get(id(n))
            if isinstance(p, ast.Subscript) and p.value is n:
                k = p.slice
                if isinstance(k, ast.Constant) and isinstance(k.value, str):
                    if isinstance(p.ctx, ast.Load):
                        reads.add(k.value)
                    else:
                        writes_unknown = True      # in-place mutation of the state
                else:
                    reads_unknown = True
            elif isinstance(p, ast.Attribute) and p.value is n:
                g = parent.get(id(p))
                if p.attr == "get" and isinstance(g, ast.Call) and g.func is p and g.args \
                        and isinstance(g.args[0], ast.Constant) and isinstance(g.args[0].value, str):
                    reads.add(g.args[0].value)
                elif p.attr in STATE_METHODS:
                    reads_unknown = True
                else:
                    reads.add(p.attr)
            else:
                reads_unknown = True                # passed on, iterated, spread, returned
    own_ids = {id(n) for n in own}
    if state is not None and any(isinstance(n, ast.Name) and n.id == state and id(n) not in own_ids for n in ast.walk(fn)):
        reads_unknown = True                        # a nested def or lambda closes over the state
    assigned = {}
    for n in own:
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name):
            assigned.setdefault(n.targets[0].id, []).append(n.value)
    returns = [fn.body] if isinstance(fn, ast.Lambda) else [n.value for n in own if isinstance(n, ast.Return)]
    for v in returns:
        if v is None or (isinstance(v, ast.Constant) and v.value is None):
            continue
        if isinstance(v, ast.Name) and len(assigned.get(v.id, [])) == 1:
            v = assigned[v.id][0]
        if isinstance(v, ast.Call) and getattr(v.func, "id", getattr(v.func, "attr", "")) == "Command":
            for kw in v.keywords:
                if kw.arg == "update":
                    k, u = _dict_keys(kw.value)
                    writes |= k
                    writes_unknown = writes_unknown or u
                elif kw.arg == "goto":
                    t, par, dyn = _const_targets(kw.value)
                    gotos += t
                    goto_parallel = goto_parallel or par
                    dynamic = "send" if "send" in (dynamic, dyn) else (dynamic or dyn)
            continue
        k, u = _dict_keys(v)
        writes |= k
        writes_unknown = writes_unknown or u
    return {"reads": sorted(reads), "reads_unknown": reads_unknown, "writes": sorted(writes),
            "writes_unknown": writes_unknown, "gotos": gotos, "goto_parallel": goto_parallel, "dynamic": dynamic}


def router_targets(fn):
    out, par, dyn = [], False, False
    returns = [fn.body] if isinstance(fn, ast.Lambda) else [n.value for n in _own_nodes(fn) if isinstance(n, ast.Return)]
    for v in returns:
        if v is None:
            continue
        t, p, d = _const_targets(v)
        out += t
        par, dyn = par or p, ("send" if "send" in (dyn, d) else (dyn or d))
    return out, par, dyn


# ------------------------------------------------------------------- schema
def schema_reducers(classes, name, seen=None):
    """(known, reducer_keys, all_keys) of a state schema class defined in the file."""
    seen = seen or set()
    if name in ("MessagesState", "AgentState"):
        return True, {"messages"}, {"messages"}
    if name not in classes or name in seen:
        return False, set(), set()
    seen.add(name)
    red, keys, known = set(), set(), True
    for b in classes[name].bases:
        bn = getattr(b, "id", getattr(b, "attr", None))
        if bn in ("TypedDict", "BaseModel", "object", "Generic", None):
            continue
        k, r, a = schema_reducers(classes, bn, seen)
        known, red, keys = known and k, red | r, keys | a
    for st in classes[name].body:
        if isinstance(st, ast.AnnAssign) and isinstance(st.target, ast.Name):
            keys.add(st.target.id)
            ann = st.annotation
            if isinstance(ann, ast.Subscript) and getattr(ann.value, "id", getattr(ann.value, "attr", "")) == "Annotated":
                red.add(st.target.id)
    return known, red, keys


# ------------------------------------------------------------------- graphs
def _key(e):
    if isinstance(e, ast.Name):
        return e.id
    if isinstance(e, ast.Attribute):
        base = _key(e.value)
        return None if base is None else base + "." + e.attr
    return None


def _is_ctor(c):
    return isinstance(c, ast.Call) and getattr(c.func, "id", getattr(c.func, "attr", "")) in ("StateGraph", "MessageGraph")


def _chain(call):
    """Unwind a.b(...).c(...) into (root expression, [(attr, call), ...]) in call order."""
    ops = []
    e = call
    while isinstance(e, ast.Call) and isinstance(e.func, ast.Attribute):
        ops.append((e.func.attr, e))
        e = e.func.value
    return e, list(reversed(ops))


def _resolve_fn(e, funcs):
    """The def/lambda a node expression names, or None (unresolved)."""
    if isinstance(e, ast.Lambda):
        return e
    if isinstance(e, ast.Name):
        return funcs.get(e.id)
    if isinstance(e, ast.Attribute):
        # only self.method / cls.method: obj.invoke could be anything
        return funcs.get(e.attr) if getattr(e.value, "id", None) in ("self", "cls") else None
    if isinstance(e, ast.Call) and getattr(e.func, "id", getattr(e.func, "attr", "")) in ("partial", "RunnableLambda") and e.args:
        return _resolve_fn(e.args[0], funcs)
    return None


def _node_name(e):
    if isinstance(e, ast.Constant) and isinstance(e.value, str):
        return e.value
    if isinstance(e, ast.Name) and e.id in ("START", "END"):
        return START if e.id == "START" else END
    return None


def extract(source, path="<memory>"):
    """Every StateGraph construction site of one file, as plain facts."""
    tree = ast.parse(source)
    funcs, classes = {}, {}
    for n in ast.walk(tree):
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
            funcs.setdefault(n.name, n)
        elif isinstance(n, ast.ClassDef):
            classes.setdefault(n.name, n)
    graphs = {}

    def graph_for(key, ctor):
        if key not in graphs:
            schema = getattr(ctor.args[0], "id", getattr(ctor.args[0], "attr", None)) if ctor.args else None
            if getattr(ctor.func, "id", getattr(ctor.func, "attr", "")) == "MessageGraph":
                schema = "MessagesState"
            graphs[key] = {"path": path, "line": ctor.lineno, "builder": "", "schema": schema, "nodes": {},
                           "edges": [], "cond": [], "dynamic_edges": False}
        return graphs[key]

    def apply(g, attr, c):
        a, kw = c.args, {k.arg: k.value for k in c.keywords}
        if attr == "add_node":
            name_e = a[0] if a else kw.get("node")
            fn_e = a[1] if len(a) > 1 else kw.get("action", kw.get("node") if a else None)
            if fn_e is None:                                  # add_node(fn)
                fn_e, name = name_e, getattr(name_e, "id", getattr(name_e, "attr", None))
            else:
                name = _node_name(name_e)
            if name is None:
                g["dynamic_edges"] = True
                return
            fn = _resolve_fn(fn_e, funcs)
            g["nodes"][name] = analyse_fn(fn) if fn is not None else None
        elif attr == "add_sequence" and a and isinstance(a[0], (ast.List, ast.Tuple)):
            prev = None
            for el in a[0].elts:
                fn_e, name = el, getattr(el, "id", getattr(el, "attr", None))
                if isinstance(el, ast.Tuple) and len(el.elts) == 2:
                    name, fn_e = _node_name(el.elts[0]), el.elts[1]
                if name is None:
                    g["dynamic_edges"] = True
                    continue
                fn = _resolve_fn(fn_e, funcs)
                g["nodes"][name] = analyse_fn(fn) if fn is not None else None
                if prev:
                    g["edges"].append([prev, name])
                prev = name
        elif attr == "add_edge" and len(a) >= 2:
            srcs = a[0].elts if isinstance(a[0], (ast.List, ast.Tuple)) else [a[0]]
            dst = _node_name(a[1])
            for s in srcs:
                sn = _node_name(s)
                if sn is None or dst is None:
                    g["dynamic_edges"] = True
                else:
                    g["edges"].append([sn, dst])
        elif attr == "set_entry_point" and a and _node_name(a[0]):
            g["edges"].append([START, _node_name(a[0])])
        elif attr == "set_finish_point" and a and _node_name(a[0]):
            g["edges"].append([_node_name(a[0]), END])
        elif attr in ("add_conditional_edges", "set_conditional_entry_point"):
            if attr == "set_conditional_entry_point":
                src, rest = START, a
            else:
                src, rest = (_node_name(a[0]) if a else None), a[1:]
            router = rest[0] if rest else kw.get("path")
            pmap = rest[1] if len(rest) > 1 else kw.get("path_map")
            targets, par, dyn = [], False, False
            fn = _resolve_fn(router, funcs) if router is not None else None
            if fn is not None:
                targets, par, dyn = router_targets(fn)
            if isinstance(pmap, ast.Dict):
                targets = [t for v in pmap.values for t in _const_targets(v)[0]]
            elif isinstance(pmap, (ast.List, ast.Tuple)):
                targets = _const_targets(pmap)[0]
            elif fn is None:
                dyn = "unresolved"
            if src is None:
                g["dynamic_edges"] = True
            else:
                g["cond"].append({"src": src, "targets": sorted(set(targets)), "parallel": par, "dynamic": dyn})

    # Builders are scoped. `graph = StateGraph(S)` in two functions of one file is
    # two graphs, not one: keying builders by bare variable name merged their
    # edges and manufactured a fork (the census's first and only rw_plain hit,
    # finos-labs/open-eago workflow.py, was exactly that and is sequential).
    # A Name lives in its innermost function, `self.x` in its innermost class, and
    # a second constructor assigned to the same name starts a second graph.
    stmts = []

    def visit(node, fscope, cscope):
        for child in ast.iter_child_nodes(node):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                visit(child, id(child), cscope)
            elif isinstance(child, ast.ClassDef):
                visit(child, fscope, id(child))
            else:
                if isinstance(child, (ast.Assign, ast.AnnAssign, ast.Expr)):
                    stmts.append((child.lineno, child.col_offset, fscope, cscope, child))
                visit(child, fscope, cscope)

    visit(tree, 0, 0)
    current, ordered = {}, []
    for _, _, fscope, cscope, n in sorted(stmts, key=lambda t: (t[0], t[1])):
        value = n.value
        if not isinstance(value, ast.Call):
            continue
        target = None
        if isinstance(n, ast.Assign) and len(n.targets) == 1:
            target = _key(n.targets[0])
        elif isinstance(n, ast.AnnAssign):
            target = _key(n.target)
        root, ops = _chain(value)
        ctor = value if _is_ctor(value) else root if _is_ctor(root) else None
        if ctor is not None:
            name = target or "line%d" % ctor.lineno
            scope = cscope if name.startswith("self.") else fscope
            g = graph_for((scope, name, ctor.lineno), ctor)
            g["builder"] = name
            current[(scope, name)] = g
            ordered.append(g)
            for attr, c in (ops if ctor is root else []):
                apply(g, attr, c)
            continue
        k = _key(root)
        if k is None:
            continue
        g = current.get((cscope if k.startswith("self.") else fscope, k))
        if g is not None:
            for attr, c in ops:
                apply(g, attr, c)
    out = []
    for g in ordered:
        if g["nodes"] or g["edges"]:
            known, red, keys = schema_reducers(classes, g["schema"]) if g["schema"] else (False, set(), set())
            g["schema_known"], g["reducers"] = known, sorted(red)
            classify(g)
            out.append(g)
    return out


# ----------------------------------------------------------- classification
def co_scheduled(g):
    """Pairs of nodes one fork releases into the same superstep: [(a, b, via)]."""
    succ = {}
    for s, d in g["edges"]:
        if d != END:
            succ.setdefault(s, set()).add(d)
    pairs = {}
    for fork, outs in succ.items():
        outs = sorted(outs)
        if len(outs) < 2:
            continue
        frontiers = [{o} for o in outs]
        seen = [set(f) for f in frontiers]
        for depth in range(1, MAX_DEPTH + 1):
            for i in range(len(frontiers)):
                for j in range(i + 1, len(frontiers)):
                    for a in frontiers[i]:
                        for b in frontiers[j]:
                            joined = any(a in seen[k] for k in range(len(seen)) if k != i) or \
                                     any(b in seen[k] for k in range(len(seen)) if k != j)
                            if a != b and not joined:
                                pairs.setdefault(tuple(sorted((a, b))), "fork:%s@%d" % (fork, depth))
            nxt = []
            for f in frontiers:
                n2 = set()
                for x in f:
                    n2 |= succ.get(x, set())
                nxt.append(n2)
            frontiers = nxt
            for k, f in enumerate(frontiers):
                seen[k] |= f
            if not any(frontiers):
                break
    lists = [c["targets"] for c in g["cond"] if c["parallel"]]
    lists += [f["gotos"] for f in g["nodes"].values() if f and f["goto_parallel"]]
    for ts in lists:
        ts = sorted(set(t for t in ts if t not in (START, END)))
        for i in range(len(ts)):
            for j in range(i + 1, len(ts)):
                pairs.setdefault((ts[i], ts[j]), "list-return")
    return [(a, b, via) for (a, b), via in sorted(pairs.items())]


def classify(g):
    red = set(g["reducers"])
    g["pairs"], worst = [], "sequential"
    for a, b, via in co_scheduled(g):
        fa, fb = g["nodes"].get(a), g["nodes"].get(b)
        rw = set()
        if fa and fb:
            rw = (set(fa["reads"]) & set(fb["writes"])) | (set(fb["reads"]) & set(fa["writes"]))
        unknown = not (fa and fb) or fa["reads_unknown"] or fb["reads_unknown"] or fa["writes_unknown"] or fb["writes_unknown"]
        plain = sorted(k for k in rw if g["schema_known"] and k not in red)
        reducer = sorted(k for k in rw if k in red)
        unk_ch = sorted(k for k in rw if not g["schema_known"] and k not in red)
        ww = sorted(set(fa["writes"]) & set(fb["writes"])) if fa and fb else []
        # an unknown side outranks a reducer-only hit: it could hide a plain one
        status = "rw_plain" if plain else "rw_unknown_channel" if unk_ch else "unknown" if unknown else \
                 "rw_reducer_only" if reducer else "parallel_clean"
        g["pairs"].append({"a": a, "b": b, "via": via, "status": status, "rw_plain": plain,
                           "rw_reducer": reducer, "rw_unknown_channel": unk_ch, "ww": ww})
        if STATUS_ORDER.index(status) < STATUS_ORDER.index(worst):
            worst = status
    kinds = [c["dynamic"] for c in g["cond"]] + [f["dynamic"] for f in g["nodes"].values() if f]
    g["send_fanout"] = "send" in kinds                  # map-reduce replication: parallel, not pair-analysed
    g["unresolved_routing"] = "unresolved" in kinds or g["dynamic_edges"]
    g["status"] = worst
    return g


# ----------------------------------------------------------------- fixtures
PRE = "import operator\nfrom typing import Annotated, TypedDict\nfrom langgraph.graph import StateGraph, START, END\n"
FIXTURES = [
    # name, source, expected status, expected co-scheduled pairs, runnable
    ("sequential_chain", PRE + '''
class S(TypedDict):
    x: int
    y: int
def a(state): return {"x": state["x"] + 1}
def b(state): return {"y": state["x"] * 2}
g = StateGraph(S)
g.add_node("a", a); g.add_node("b", b)
g.add_edge(START, "a"); g.add_edge("a", "b"); g.add_edge("b", END)
GRAPH = g.compile(); INPUT = {"x": 1, "y": 0}
''', "sequential", [], True),
    ("fanout_disjoint_keys", PRE + '''
class S(TypedDict):
    q: str
    docs: str
    web: str
    answer: str
def retrieve(state): return {"docs": "d:" + state["q"]}
def search(state): return {"web": "w:" + state["q"]}
def generate(state): return {"answer": state["docs"] + state["web"]}
g = StateGraph(S)
g.add_node("retrieve", retrieve); g.add_node("search", search); g.add_node("generate", generate)
g.add_edge(START, "retrieve"); g.add_edge(START, "search")
g.add_edge(["retrieve", "search"], "generate"); g.add_edge("generate", END)
GRAPH = g.compile(); INPUT = {"q": "x", "docs": "", "web": "", "answer": ""}
''', "parallel_clean", [("retrieve", "search")], True),
    ("editor_and_summarizer", PRE + '''
class S(TypedDict):
    doc: str
    summary: str
def edit(state): return {"doc": state["doc"] + " v2"}
def summarize(state): return {"summary": "sum(" + state["doc"] + ")"}
g = StateGraph(S)
g.add_node("edit", edit); g.add_node("summarize", summarize)
g.add_edge(START, "edit"); g.add_edge(START, "summarize")
g.add_edge("edit", END); g.add_edge("summarize", END)
GRAPH = g.compile(); INPUT = {"doc": "v1", "summary": ""}
''', "rw_plain", [("edit", "summarize")], True),
    ("parallel_agents_on_a_reducer", PRE + '''
class S(TypedDict):
    messages: Annotated[list, operator.add]
def agent_a(state): return {"messages": ["a saw %d" % len(state["messages"])]}
def agent_b(state): return {"messages": ["b saw %d" % len(state["messages"])]}
g = StateGraph(S)
g.add_node("agent_a", agent_a); g.add_node("agent_b", agent_b)
g.add_edge(START, "agent_a"); g.add_edge(START, "agent_b")
g.add_edge("agent_a", END); g.add_edge("agent_b", END)
GRAPH = g.compile(); INPUT = {"messages": ["hi"]}
''', "rw_reducer_only", [("agent_a", "agent_b")], True),
    ("exclusive_router", PRE + '''
class S(TypedDict):
    x: int
    out: str
def start(state): return {"x": state["x"]}
def route(state): return "big" if state["x"] > 5 else "small"
def big(state): return {"out": "big"}
def small(state): return {"out": "small:%d" % state["x"]}
g = StateGraph(S)
g.add_node("start", start); g.add_node("big", big); g.add_node("small", small)
g.add_edge(START, "start"); g.add_conditional_edges("start", route, {"big": "big", "small": "small"})
g.add_edge("big", END); g.add_edge("small", END)
GRAPH = g.compile(); INPUT = {"x": 1, "out": ""}
''', "sequential", [], True),
    ("equal_depth_chains", PRE + '''
class S(TypedDict):
    plan: str
    draft: str
    note: str
    review: str
def a(state): return {"note": "n"}
def b(state): return {"draft": "d"}
def c(state): return {"plan": state["plan"] + "+c"}
def d(state): return {"review": "r(" + state["plan"] + ")"}
g = StateGraph(S)
g.add_node("a", a); g.add_node("b", b); g.add_node("c", c); g.add_node("d", d)
g.add_edge(START, "a"); g.add_edge(START, "b"); g.add_edge("a", "c"); g.add_edge("b", "d")
g.add_edge("c", END); g.add_edge("d", END)
GRAPH = g.compile(); INPUT = {"plan": "p", "draft": "", "note": "", "review": ""}
''', "rw_plain", [("a", "b"), ("c", "d")], True),
    ("unresolved_node_function", PRE + '''
from somewhere import imported_agent
class S(TypedDict):
    doc: str
def edit(state): return {"doc": state["doc"] + "!"}
g = StateGraph(S)
g.add_node("edit", edit); g.add_node("agent", imported_agent)
g.add_edge(START, "edit"); g.add_edge(START, "agent")
''', "unknown", [("agent", "edit")], False),
    ("state_passed_on_is_unknown", PRE + '''
class S(TypedDict):
    doc: str
    out: str
def helper(s): return s
def edit(state): return {"doc": "x"}
def opaque(state):
    helper(state)
    return {"out": "y"}
g = StateGraph(S)
g.add_node("edit", edit); g.add_node("opaque", opaque)
g.add_edge(START, "edit"); g.add_edge(START, "opaque")
''', "unknown", [("edit", "opaque")], False),
    ("class_methods_and_chained_builder", PRE + '''
class S(TypedDict):
    doc: str
    summary: str
class App:
    def edit(self, state): return {"doc": state.get("doc", "") + " v2"}
    def summarize(self, state): return {"summary": state["doc"]}
    def build(self):
        self.builder = StateGraph(S)
        self.builder.add_node("edit", self.edit).add_node("summarize", self.summarize)
        self.builder.add_edge(START, "edit").add_edge(START, "summarize")
        return self.builder.compile()
GRAPH = App().build(); INPUT = {"doc": "v1", "summary": ""}
''', "rw_plain", [("edit", "summarize")], True),
    ("two_builders_with_one_name", PRE + '''
class S(TypedDict):
    doc: str
    out: str
def first(state): return {"doc": state["doc"] + "1"}
def second(state): return {"out": state["doc"]}
def build_full():
    graph = StateGraph(S)
    graph.add_node("first", first); graph.add_node("second", second)
    graph.set_entry_point("first"); graph.add_edge("first", "second"); graph.add_edge("second", END)
    return graph.compile()
def build_resume():
    graph = StateGraph(S)
    graph.add_node("second", second)
    graph.set_entry_point("second"); graph.add_edge("second", END)
    return graph.compile()
GRAPH = build_full(); INPUT = {"doc": "d", "out": ""}
''', ["sequential", "sequential"], [], True),
    ("unknown_schema_channel", PRE + '''
from app.state import ImportedState
def edit(state): return {"doc": "v2"}
def summarize(state): return {"summary": state["doc"]}
g = StateGraph(ImportedState)
g.add_node(edit); g.add_node(summarize)
g.set_entry_point("edit"); g.add_edge(START, "summarize")
''', "rw_unknown_channel", [("edit", "summarize")], False),
]


def selftest():
    fails = 0
    for name, src, want_status, want_pairs, _ in FIXTURES:
        gs = extract(src, name)
        want = want_status if isinstance(want_status, list) else [want_status]
        got_pairs = sorted((p["a"], p["b"]) for g in gs for p in g["pairs"])
        ok = [g["status"] for g in gs] == want and got_pairs == sorted(tuple(sorted(p)) for p in want_pairs)
        if not ok:
            fails += 1
            print("SELFTEST FAIL  %s: statuses %r (want %r), pairs %r (want %r)" % (
                name, [g["status"] for g in gs], want, got_pairs, want_pairs))
    # a dependency mismatch raises SystemError, not ImportError: the probe must absorb it
    def boom():
        raise SystemError("pydantic-core mismatch")
    try:
        got = probe_langgraph(boom)
    except BaseException as e:  # noqa: BLE001
        got = ("ESCAPED", type(e).__name__)
    if got != (False, "SystemError: pydantic-core mismatch"):
        fails += 1
        print("SELFTEST FAIL  the import probe let a non-ImportError through or misreported it: %r" % (got,))
    # an unimportable langgraph must be reported as NOT RUN (2), never as a disagreement (1)
    import contextlib
    import io
    real = globals()["probe_langgraph"]
    globals()["probe_langgraph"] = lambda: (False, "SystemError: simulated dependency mismatch")
    buf = io.StringIO()
    try:
        with contextlib.redirect_stdout(buf):
            code = oracle()
    finally:
        globals()["probe_langgraph"] = real
    if code != ORACLE_NOT_RUN or "NOT RUN" not in buf.getvalue():
        fails += 1
        print("SELFTEST FAIL  oracle on an unimportable langgraph: exit %r, output %r (want exit 2 and NOT RUN)" % (code, buf.getvalue()[:80]))
    print("selftest: %d fixtures and 2 oracle-mode checks, %d failed" % (len(FIXTURES), fails))
    return 1 if fails else 0


# ------------------------------------------------------------------- oracle
class _Rec(dict):
    """A state that remembers which keys a node function read."""
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.read = set()

    def __getitem__(self, k):
        self.read.add(k)
        return super().__getitem__(k)

    def get(self, k, d=None):
        self.read.add(k)
        return super().get(k, d)


ORACLE_AGREE, ORACLE_DISAGREE, ORACLE_NOT_RUN, ORACLE_FIXTURE_ERROR = 0, 1, 2, 3


def _import_langgraph():
    from langgraph.graph import END, START, StateGraph  # noqa: F401
    import importlib.metadata as md
    return md.version("langgraph")


def probe_langgraph(importer=_import_langgraph):
    """(ok, version or reason). ANY failure while importing counts: a broken
    dependency raises SystemError or AttributeError inside the import, not
    ImportError."""
    try:
        return True, importer()
    except KeyboardInterrupt:
        raise
    except BaseException as e:  # noqa: BLE001
        first = (str(e).splitlines() or [""])[0][:160]
        return False, "%s: %s" % (type(e).__name__, first)


def oracle():
    """Execute each runnable fixture on real LangGraph and demand static == dynamic:
    the pairs that ran in one superstep, and each node's read and written keys."""
    ok, info = probe_langgraph()
    if not ok:
        print("oracle: NOT RUN -- langgraph cannot be imported by this python3 (%s). "
              "That is an environment failure and says nothing about the front end." % info)
        return ORACLE_NOT_RUN
    fails = 0
    errors = 0
    ran = 0
    for name, src, _, want_pairs, runnable in FIXTURES:
        if not runnable:
            continue
        ran += 1
        static = extract(src, name)[0]
        env = {}
        steps = {}
        try:
            exec(compile(src, name, "exec"), env)
            for ev in env["GRAPH"].stream(env["INPUT"], stream_mode="debug"):
                if ev.get("type") == "task" and not ev["payload"]["name"].startswith("__"):
                    steps.setdefault(ev["step"], set()).add(ev["payload"]["name"])
        except Exception as e:  # noqa: BLE001
            errors += 1
            print("ORACLE ERROR  %s could not be executed (%s: %s) -- an environment failure, not a disagreement" % (
                name, type(e).__name__, (str(e).splitlines() or [""])[0][:140]))
            continue
        dyn_pairs = sorted(tuple(sorted((a, b))) for s in steps.values() for a in s for b in s if a < b)
        st_pairs = sorted((p["a"], p["b"]) for p in static["pairs"])
        if dyn_pairs != st_pairs:
            fails += 1
            print("ORACLE FAIL  %s: co-scheduled pairs static %r, executed %r" % (name, st_pairs, dyn_pairs))
        holder = env.get("App")() if "App" in env else None
        for node, facts in static["nodes"].items():
            fn = getattr(holder, node) if holder is not None and hasattr(holder, node) else env.get(node)
            if fn is None or facts is None:
                continue
            rec = _Rec(env["INPUT"])
            out = fn(rec) or {}
            if sorted(rec.read) != facts["reads"] or sorted(out) != facts["writes"]:
                fails += 1
                print("ORACLE FAIL  %s.%s: reads static %r executed %r; writes static %r executed %r" % (
                    name, node, facts["reads"], sorted(rec.read), facts["writes"], sorted(out)))
    print("oracle: %d fixtures executed on langgraph %s, %d disagreement(s) between static and executed, %d could not be executed" % (
        ran - errors, info, fails, errors))
    return ORACLE_DISAGREE if fails else ORACLE_FIXTURE_ERROR if errors else ORACLE_AGREE


def main():
    if "--selftest" in sys.argv:
        return selftest()
    if "--oracle" in sys.argv:
        return oracle()
    for p in sys.argv[1:]:
        with open(p, encoding="utf-8", errors="replace") as fh:
            for g in extract(fh.read(), p):
                print(json.dumps(g, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
