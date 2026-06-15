# Does the L3 discipline (commit tool effects in the LLM's tool_calls order) fix it
# on the SAME tools / message that ToolNode reordered? A minimal sequenced executor.
import asyncio, random
from langchain_core.messages import AIMessage, ToolMessage
from langchain_core.tools import tool

EFFECT_LOG = []; DELAYS = {}
def mk(i):
    async def _f(note: str = "") -> str:
        await asyncio.sleep(DELAYS[i]); EFFECT_LOG.append(i); return f"step {i} committed"
    _f.__name__ = f"step_{i}"; _f.__doc__ = f"step {i}"
    return tool(_f)
TOOLS = {f"step_{i}": mk(i) for i in range(5)}

def ordered_calls():
    return [{"name": f"step_{i}", "args": {"note": f"do {i}"}, "id": f"c{i}"} for i in range(5)]

def a6(io, co): return len(io)>=2 and len(io)==len(co) and io != co

# L3 sequencer: await each tool call in tool_calls order before issuing the next.
async def sequenced_execute(calls):
    msgs = []
    for c in calls:
        out = await TOOLS[c["name"]].ainvoke(c["args"])     # awaited -> effect commits before next
        msgs.append(ToolMessage(content=str(out), name=c["name"], tool_call_id=c["id"]))
    return msgs

async def main():
    global DELAYS, EFFECT_LOG
    io = list(range(5))
    print("L3-sequenced ToolNode (await in tool_calls order) on the SAME reordering inputs:\n")
    cfgs = [("heterogeneous step0 slowest", {0:0.25,1:0.20,2:0.15,3:0.10,4:0.05})]
    for t in range(4):
        random.seed(100+t)
        cfgs.append((f"random mixed #{t}", {i: round(random.uniform(0.01,0.20),3) for i in range(5)}))
    for label, d in cfgs:
        DELAYS = d; EFFECT_LOG = []
        await sequenced_execute(ordered_calls())
        co = list(EFFECT_LOG)
        print(f"  [{label:24}] EFFECT-order co={co}  a6={a6(io,co)}")
asyncio.run(main())