#!/usr/bin/env python3
"""
white_box_proxy.py -- faithful generation-time read capture for the Letta A1 probe.

Sits between Letta and OpenAI as a verbatim passthrough on /v1/*. On every
/v1/chat/completions call it records, with a real timestamp, the EXACT context
Letta rendered into the agent's prompt -- including the shared memory block as
the model actually saw it at generation time -- then forwards the request
unchanged to OpenAI and relays the response (streaming or not) untouched.

That logged block is the faithful read_value Definition A1 requires: it is what
the agent's generation was grounded in, not a post-hoc snapshot. Joined with the
probe's captured writes (memory_insert args) it yields admissible OpRecords for
the verified detector -- so A1 can be certified or cleanly refuted in the wild.

NO changes to Letta. Use the stock Docker image and point it here:
  Linux : docker run --network host -e OPENAI_API_KEY=<real key> \
                 -e OPENAI_API_BASE=http://localhost:8299/v1 ... letta/letta:latest
  Mac/Win: -e OPENAI_API_BASE=http://host.docker.internal:8299/v1
The proxy reads the real key from Letta's forwarded Authorization header and
forwards it upstream, so you set the real key on Letta as usual.

Run:
  pip install fastapi uvicorn httpx
  python white_box_proxy.py --port 8299 --log proxy_reads.jsonl
"""
import os
import re
import sys
import json
import time
import asyncio
import argparse
import datetime

try:
    import httpx
    import uvicorn
    from fastapi import FastAPI, Request
    from fastapi.responses import StreamingResponse, JSONResponse
except Exception as e:  # pragma: no cover
    sys.stderr.write("missing deps; run: pip install fastapi uvicorn httpx\n")
    raise

app = FastAPI()


class Cfg:
    upstream = os.environ.get("WB_UPSTREAM", "https://api.openai.com")
    logpath = os.environ.get("WB_LOG", "proxy_reads.jsonl")
    block_label = os.environ.get("WB_BLOCK_LABEL", "shared_plan")


_seq = 0
_seq_lock = asyncio.Lock()


def _content_text(m):
    c = m.get("content")
    if isinstance(c, str):
        return c
    if isinstance(c, list):  # content parts
        parts = []
        for p in c:
            if isinstance(p, dict):
                parts.append(p.get("text") or p.get("content") or json.dumps(p))
            else:
                parts.append(str(p))
        return "\n".join(parts)
    return "" if c is None else json.dumps(c)


def _role_text(messages, role):
    return "\n".join(_content_text(m) for m in messages if m.get("role") == role)


def parse_marker(user_text):
    """Recover (agent, round) from the probe's marker, e.g. [agent_3|r2]."""
    m = re.search(r"\[(agent_\d+)\s*\|\s*(r\w+)\]", user_text or "")
    return (m.group(1), m.group(2)) if m else (None, None)


def parse_block(system_text, label):
    """Best-effort extraction of the shared block as Letta rendered it into the
    system prompt. Several render formats are tried; the full system_text is
    always logged too, so offline re-parsing is always possible."""
    if not system_text:
        return None
    # 1) XML-ish <label> ... </label>
    m = re.search(rf"<{re.escape(label)}[^>]*>(.*?)</{re.escape(label)}>",
                  system_text, re.S)
    if m:
        return m.group(1).strip()
    # 2) markdown-ish "### label" or "label:" header up to the next block/header
    m = re.search(rf"(?:^|\n)\s*#*\s*{re.escape(label)}\s*[:\n](.*?)"
                  rf"(?=\n\s*#|\n\s*<|\n\s*[A-Za-z_][A-Za-z0-9_ ]*:|\Z)",
                  system_text, re.S)
    if m:
        return m.group(1).strip()
    return None



def _collect_text(data):
    """Return (system_text, user_text) from EITHER a chat-completions body
    (messages[]) or a Responses-API body (instructions + input[])."""
    sys_parts, usr_parts = [], []
    msgs = data.get("messages")
    if isinstance(msgs, list):
        for m in msgs:
            t = _content_text(m)
            (sys_parts if m.get("role") == "system" else usr_parts).append(t)
    instr = data.get("instructions")
    if isinstance(instr, str) and instr:
        sys_parts.append(instr)
    inp = data.get("input")
    if isinstance(inp, str):
        usr_parts.append(inp)
    elif isinstance(inp, list):
        for it in inp:
            if isinstance(it, dict):
                t = _content_text(it)
                role = it.get("role")
                (sys_parts if role in ("system", "developer") else usr_parts).append(t)
            elif isinstance(it, str):
                usr_parts.append(it)
    return ("\n".join(p for p in sys_parts if p),
            "\n".join(p for p in usr_parts if p))


async def _log(path, body_bytes):
    global _seq
    try:
        data = json.loads(body_bytes)
    except Exception:
        return
    sys_t, usr_t = _collect_text(data)
    agent, rnd = parse_marker(usr_t)
    if agent is None:
        agent, rnd = parse_marker(sys_t)   # marker may ride along in context
    block = parse_block(sys_t, Cfg.block_label)
    async with _seq_lock:
        seq = _seq
        _seq += 1
    rec = {
        "seq": seq,
        "ts_wall": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "ts_mono": time.monotonic(),
        "path": path,
        "model": data.get("model"),
        "agent": agent,
        "round": rnd,
        "read_block": block,        # FAITHFUL generation-time read (parsed)
        "system_text": sys_t,       # full fallback for offline re-parse
        "user_text": usr_t,
        "raw": data,                # full request body, for exact offline re-parse
    }
    try:
        with open(Cfg.logpath, "a") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
    except Exception as e:  # never break forwarding because logging failed
        sys.stderr.write(f"[proxy] log error: {e}\n")
    tag = f"agent={agent} round={rnd} block_chars={len(block) if block else 'NONE'}"
    sys.stderr.write(f"[proxy] #{seq} POST {path}  {tag}\n")


async def _forward(request, body, path):
    url = Cfg.upstream.rstrip("/") + path
    # forward headers verbatim except hop-by-hop / length; force identity encoding
    headers = {k: v for k, v in request.headers.items()
               if k.lower() not in ("host", "content-length", "accept-encoding")}
    headers["accept-encoding"] = "identity"
    client = httpx.AsyncClient(timeout=None)
    upstream_req = client.build_request(
        request.method, url, headers=headers, content=body,
        params=dict(request.query_params),
    )
    upstream = await client.send(upstream_req, stream=True)

    async def gen():
        try:
            async for chunk in upstream.aiter_raw():
                yield chunk
        finally:
            await upstream.aclose()
            await client.aclose()

    drop = ("content-length", "transfer-encoding", "content-encoding", "connection")
    resp_headers = {k: v for k, v in upstream.headers.items()
                    if k.lower() not in drop}
    return StreamingResponse(
        gen(),
        status_code=upstream.status_code,
        headers=resp_headers,
        media_type=upstream.headers.get("content-type"),
    )


@app.api_route("/v1/{path:path}", methods=["GET", "POST", "PUT", "DELETE", "PATCH"])
async def proxy_all(request: Request, path: str):
    body = await request.body()
    if request.method == "POST" and ("chat/completions" in path or "responses" in path):
        await _log("/v1/" + path, body)
    return await _forward(request, body, "/v1/" + path)


@app.get("/__wb_health")
async def health():
    return JSONResponse({"ok": True, "upstream": Cfg.upstream, "log": Cfg.logpath,
                         "captured": _seq})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=int, default=8299)
    ap.add_argument("--host", default="0.0.0.0")
    ap.add_argument("--upstream", default=Cfg.upstream,
                    help="real LLM endpoint to forward to (default OpenAI)")
    ap.add_argument("--log", default=Cfg.logpath)
    ap.add_argument("--block-label", default=Cfg.block_label,
                    help="shared memory block label to parse from the system prompt")
    args = ap.parse_args()
    Cfg.upstream = args.upstream
    Cfg.logpath = args.log
    Cfg.block_label = args.block_label
    sys.stderr.write(
        f"[proxy] forwarding /v1/* -> {Cfg.upstream}\n"
        f"[proxy] logging chat reads -> {Cfg.logpath} (block label '{Cfg.block_label}')\n"
        f"[proxy] point Letta at  OPENAI_API_BASE=http://<host>:{args.port}/v1\n"
    )
    uvicorn.run(app, host=args.host, port=args.port, log_level="warning")


if __name__ == "__main__":
    main()