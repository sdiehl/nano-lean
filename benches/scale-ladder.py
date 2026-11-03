#!/usr/bin/env python3
"""Rescale the arena beta-ladder export to n binders.

usage: scale-ladder.py BETA_LADDER_NDJSON N OUT

Keeps every line of the arena export except the theorem and appends a fresh ladder
(fun x1 => ... (fun xn => x1 + (... + (xn + 0))) 0 ... ) 0 = 0 with new expression ids.
"""

import json
import sys
from pathlib import Path


def scale(src: str, n: int, out: str) -> None:
    lines = Path(src).read_text().splitlines()
    objs = [json.loads(line) for line in lines]
    exprs = {o["ie"]: o for o in objs if "ie" in o}
    thm = next(o for o in objs if "thm" in o)

    def app(i: int) -> tuple[int, int]:
        a = exprs[i]["app"]
        return a["fn"], a["arg"]

    eq_lhs, zero = app(thm["thm"]["type"])
    eq_nat, ladder = app(eq_lhs)
    lam = exprs[app(ladder)[0]]["lam"]
    body = lam["body"]
    while "lam" in exprs[app(body)[0]]:
        body = exprs[app(body)[0]]["lam"]["body"]
    add = app(app(body)[0])[0]

    next_id = max(exprs) + 1
    new = []

    def emit(obj: dict) -> int:
        nonlocal next_id
        obj["ie"] = next_id
        new.append(json.dumps(obj))
        next_id += 1
        return next_id - 1

    e = zero
    for i in range(n):
        x = emit({"bvar": i})
        e = emit({"app": {"fn": emit({"app": {"fn": add, "arg": x}}), "arg": e}})
    for _ in range(n):
        f = emit(
            {
                "lam": {
                    "binderInfo": "default",
                    "body": e,
                    "name": lam["name"],
                    "type": lam["type"],
                }
            }
        )
        e = emit({"app": {"fn": f, "arg": zero}})
    ty = emit({"app": {"fn": emit({"app": {"fn": eq_nat, "arg": e}}), "arg": zero}})
    new.append(json.dumps({"thm": {**thm["thm"], "type": ty}}))
    kept = [line for line, o in zip(lines, objs, strict=True) if o is not thm]
    Path(out).write_text("\n".join(kept + new) + "\n")


if __name__ == "__main__":
    scale(sys.argv[1], int(sys.argv[2]), sys.argv[3])
