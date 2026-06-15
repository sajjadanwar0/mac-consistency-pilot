import asyncio, random
from typing import Annotated, TypedDict
from langchain_core.messages import AIMessage
from langchain_core.tools import tool
from langgraph.prebuilt import ToolNode
from langgraph.graph import StateGraph, START, END
from langgraph.graph.message import add_messages

EFFECT_LOG = []
DELAYS = {}

def mk(i):
    async def _f(note: str = "") -> str:
        await asyncio.sleep(DELAYS[i])     # real concurrency point (models tool latency)
        EFFECT_LOG.append(i)               # <-- the order-sensitive side effect commits here
        return f"step {i} committed"
    _f.__name__ = f"step_{i}"
    _f.__doc__ = f"Perform ordered step {i} against the shared system."
    return tool(_f)

TOOLS = [mk(i) for i in range(5)]

class S(TypedDict):
    messages: Annotated[list, add_messages]

g = StateGraph(S)
g.add_node("tools", ToolNode(TOOLS))
g.add_edge(START, "tools")
g.add_edge("tools", END)
app = g.compile()

def ordered_msg():
    # LLM emits calls in INTENDED order step_0..step_4
    return AIMessage(content="", tool_calls=[
        {"name": f"step_{i}", "args": {"note": f"do {i}"}, "id": f"c{i}"} for i in range(5)])

def a6_witness(io, co):
    return len(io) >= 2 and len(io) == len(co) and io != co
def inversions(co):
    return sum(1 for i in range(len(co)) for j in range(i+1,len(co)) if co[i] > co[j])

async def run(delays, label, trials=1):
    global DELAYS, EFFECT_LOG
    io = list(range(5))
    print(f"\n[{label}]  delays(by step)={[delays[i] for i in range(5)]}")
    for t in range(trials):
        DELAYS = delays; EFFECT_LOG = []
        out = await app.ainvoke({"messages": [ordered_msg()]})
        co = list(EFFECT_LOG)
        tmsgs = [m for m in out["messages"] if m.__class__.__name__ == "ToolMessage"]
        msg_order = [int(m.name.split('_')[1]) for m in tmsgs]
        print(f"  io={io}  EFFECT-order co={co}  a6={a6_witness(io,co)} (inv={inversions(co)})  "
              f"| ToolMessage-order={msg_order}")

async def main():
    print("LangGraph ToolNode 1.2.5 -- is the LLM's intended tool-EFFECT order preserved?")
    print("io = tool_calls order emitted = [0,1,2,3,4]\n")
    await run({0:0.25,1:0.20,2:0.15,3:0.10,4:0.05}, "heterogeneous: step0 slowest (a slow first action)")
    await run({i:0.02 for i in range(5)}, "uniform latency", trials=3)
    for t in range(4):
        random.seed(100+t)
        await run({i: round(random.uniform(0.01,0.20),3) for i in range(5)}, f"random mixed latency #{t}")

asyncio.run(main())