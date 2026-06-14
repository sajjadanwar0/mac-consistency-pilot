"""
production_scenarios.py - Six cookbook-derived multi-agent scenarios.

v4 CHANGES vs v3
  - stateful_tools mapping now uses (kind, namespace) tuples instead of
    bare strings. kind in {"read", "write"}.

The six scenarios are unchanged behaviourally; only the shared_workspace
declaration now distinguishes read_workspace (kind="read") from
write_workspace (kind="write").
"""

from __future__ import annotations
import random
from typing import Callable



def make_search_tool(seed: int):
    rng = random.Random(seed)
    cache: dict[str, str] = {}
    def web_search(query: str) -> str:
        if query in cache:
            return cache[query]
        snippets = [
            f"According to {rng.choice(['recent', 'historical', '2024'])} sources, "
            f"{query} is associated with "
            f"{rng.choice(['theory X', 'mechanism Y', 'system Z'])}.",
            f"Key paper on {query}: published "
            f"{rng.randint(2018, 2024)} in "
            f"{rng.choice(['Nature', 'Science', 'NeurIPS', 'PLDI'])}.",
        ]
        cache[query] = " ".join(snippets)
        return cache[query]
    return web_search


def make_calc_tool():
    def calculator(expression: str) -> str:
        try:
            allowed = set("0123456789+-*/.() ")
            if not all(c in allowed for c in expression):
                return "ERROR: invalid characters"
            return str(eval(expression))
        except Exception as e:
            return f"ERROR: {e}"
    return calculator


def make_summarize_tool():
    def summarize(text: str) -> str:
        return text[:200]
    return summarize


def make_code_tool():
    cache: dict[str, str] = {}
    def run_python(code: str) -> str:
        if code in cache:
            return cache[code]
        cache[code] = f"Output: function executed, returned {hash(code) % 1000}"
        return cache[code]
    return run_python



def make_workspace_tools():
    state: dict[str, str] = {}

    def read_workspace(slot: str) -> str:
        return state.get(slot, "EMPTY")

    def write_workspace(slot: str, value: str) -> str:
        state[slot] = value
        return f"OK: workspace[{slot}] = {value[:120]}"

    return read_workspace, write_workspace



def scenario_research_collab(seed: int) -> dict:
    return {
        "name": "research_collab",
        "agents": [
            ("researcher",
             "You are a researcher. Use web_search to gather facts about the topic, "
             "then call summarize on the most important finding. "
             "Reply with 'HANDOFF' when you have a summary. Maximum 3 tool calls."),
            ("analyst",
             "You are an analyst. Read the researcher's summary, then call "
             "web_search to verify one claim and summarize what you found. "
             "Reply 'DONE' when complete. Maximum 3 tool calls."),
        ],
        "tools": {
            "web_search": make_search_tool(seed),
            "summarize": make_summarize_tool(),
        },
        "task": "Research the topic: 'memory consistency in distributed systems'.",
        "max_turns": 8,
        "stateful_tools": {},
    }


def scenario_supervisor(seed: int) -> dict:
    return {
        "name": "supervisor",
        "agents": [
            ("supervisor",
             "You are a supervisor. Decide whether 'researcher' or 'calculator' "
             "should handle the next step. Reply with just 'researcher' or "
             "'calculator' or 'DONE'. Do not call tools yourself."),
            ("researcher",
             "Use web_search exactly once if asked. Then reply with a "
             "one-sentence summary. Don't call tools twice."),
            ("calculator",
             "Use the calculator tool exactly once if needed, then reply "
             "with the numeric answer."),
        ],
        "tools": {
            "web_search": make_search_tool(seed),
            "calculator": make_calc_tool(),
        },
        "task": "Estimate the publication year of the first paper on snapshot "
                "isolation and add 30 to it.",
        "max_turns": 10,
        "stateful_tools": {},
    }


def scenario_hierarchical(seed: int) -> dict:
    return {
        "name": "hierarchical",
        "agents": [
            ("top_supervisor",
             "Decide whether the question is a 'research' question or an "
             "'analysis' question. Reply with one of those words, or 'DONE'."),
            ("research_lead",
             "If asked to research, call web_search once and summarize."),
            ("analysis_lead",
             "If asked to analyse, call calculator once and report the result."),
        ],
        "tools": {
            "web_search": make_search_tool(seed),
            "calculator": make_calc_tool(),
            "summarize": make_summarize_tool(),
        },
        "task": "Find the year of the first SSI paper, then compute that year "
                "minus 1990.",
        "max_turns": 10,
        "stateful_tools": {},
    }


def scenario_code_review(seed: int) -> dict:
    return {
        "name": "code_review",
        "agents": [
            ("coder",
             "Write a small Python function as a string, then call run_python "
             "on it. After receiving feedback, you may revise and call "
             "run_python once more. Reply 'HANDOFF' to give to the reviewer."),
            ("reviewer",
             "After coder hands off, read their code, call run_python on a "
             "small modified version, and reply 'APPROVED' or 'NEEDS_WORK: ...'."),
        ],
        "tools": {
            "run_python": make_code_tool(),
        },
        "task": "Write and review a function that computes the factorial of n.",
        "max_turns": 8,
        "stateful_tools": {},
    }


def scenario_customer_triage(seed: int) -> dict:
    return {
        "name": "customer_triage",
        "agents": [
            ("triager",
             "Classify the ticket as 'billing' or 'technical'. Reply just that word."),
            ("billing_agent",
             "If billing-related, use the calculator to compute the refund "
             "($20 per day overcharge), then reply with the dollar amount."),
            ("tech_agent",
             "If technical, use web_search for one troubleshooting tip, then "
             "reply with a one-sentence answer."),
        ],
        "tools": {
            "web_search": make_search_tool(seed),
            "calculator": make_calc_tool(),
        },
        "task": "Customer ticket: 'My subscription was charged for 5 extra days "
                "and I cannot log in to the dashboard.'",
        "max_turns": 8,
        "stateful_tools": {},
    }


def scenario_shared_workspace(seed: int) -> dict:
    """Three agents share a typed workspace. The read_workspace tool is
    declared kind="read" so it does NOT pollute write_set; the
    write_workspace tool is declared kind="write" and its extracted
    `value` field is what's compared against subsequent reads. A_1
    therefore fires only on actual stale-read patterns (older content
    observed before a later content-update to the same slot)."""
    read_workspace, write_workspace = make_workspace_tools()
    return {
        "name": "shared_workspace",
        "agents": [
            ("planner",
             "You manage the workspace. STEP 1: call write_workspace with "
             "slot='task' and a one-sentence task description for the team. "
             "STEP 2: call read_workspace with slot='progress' to check status. "
             "STEP 3: based on progress, call write_workspace with slot='task' "
             "to update the task (REVISE the task). STEP 4: reply 'HANDOFF'."),
            ("executor",
             "STEP 1: call read_workspace with slot='task' to see the task. "
             "STEP 2: call write_workspace with slot='progress' and "
             "value='executing <task>'. STEP 3: reply 'HANDOFF'."),
            ("monitor",
             "STEP 1: call read_workspace with slot='task'. "
             "STEP 2: call read_workspace with slot='progress'. "
             "STEP 3: call write_workspace with slot='notes' and a brief observation. "
             "STEP 4: reply 'DONE'."),
        ],
        "tools": {
            "read_workspace": read_workspace,
            "write_workspace": write_workspace,
        },
        "task": "Coordinate a small task with planner, executor, monitor.",
        "max_turns": 14,
        "stateful_tools": {
            "read_workspace": ("read", "ws"),
            "write_workspace": ("write", "ws"),
        },
    }


SCENARIOS: dict[str, Callable] = {
    "research_collab": scenario_research_collab,
    "supervisor": scenario_supervisor,
    "hierarchical": scenario_hierarchical,
    "code_review": scenario_code_review,
    "customer_triage": scenario_customer_triage,
    "shared_workspace": scenario_shared_workspace,
}