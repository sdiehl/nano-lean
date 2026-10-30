#!/usr/bin/env python3
"""A/B the kernel benches: a git revision against the working tree, interleaved in one lease.

    benches/compare.py [BASE] [FILTER] [--reps N] [--rounds N]

BASE (default HEAD) is extracted with git archive and built with the working tree's harness
and suite, so both sides run the same measurement code on the same fixtures. Runs go
A B B A ... under .local/benchmark.lock. Each side's best run is compared, which also drops
the high first run after a build, and the spread between base runs is the noise floor.
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LOCK = ROOT / ".local" / "benchmark.lock"
TREES = ROOT / "target" / "nl-bench" / "trees"
BENCH = '\n[[bench]]\nname = "kernel"\nharness = false\n'


def sh(*args, **kw):
    return subprocess.run(args, check=True, text=True, capture_output=True, **kw).stdout


def build(tree):
    out = sh(
        "cargo",
        "bench",
        "--bench",
        "kernel",
        "--no-run",
        "--message-format=json",
        cwd=tree,
    )
    for line in out.splitlines():
        m = json.loads(line)
        if (
            m.get("reason") == "compiler-artifact"
            and m["target"]["name"] == "kernel"
            and m.get("executable")
        ):
            return m["executable"]
    sys.exit(f"no kernel bench executable built in {tree}")


def base_tree(rev):
    sha = sh("git", "rev-parse", "--verify", f"{rev}^{{commit}}", cwd=ROOT).strip()
    tree = TREES / sha[:12]
    if not tree.exists():
        tree.mkdir(parents=True)
        archive = subprocess.Popen(
            ["git", "archive", sha], cwd=ROOT, stdout=subprocess.PIPE
        )
        subprocess.run(["tar", "-x", "-C", tree], stdin=archive.stdout, check=True)
        if archive.wait():
            sys.exit(f"git archive {sha} failed")
    (tree / "benches").mkdir(exist_ok=True)
    shutil.copy(ROOT / "benches" / "kernel.rs", tree / "benches" / "kernel.rs")
    manifest = tree / "Cargo.toml"
    if 'name = "kernel"' not in manifest.read_text():
        manifest.write_text(manifest.read_text() + BENCH)
    return sha, tree


def alive(pid):
    try:
        os.kill(pid, 0)
        return True
    except (OSError, TypeError):
        return False


def acquire():
    if LOCK.exists():
        held = json.loads(LOCK.read_text() or "{}")
        if "finished" not in held and alive(held.get("pid")):
            sys.exit(f"benchmark lease held: {held}")
    LOCK.parent.mkdir(exist_ok=True)
    lease = {
        "pid": os.getpid(),
        "started": datetime.now().astimezone().isoformat(),
        "command": sys.argv,
    }
    LOCK.write_text(json.dumps(lease))
    return lease


def release(lease, code):
    lease.update(finished=datetime.now().astimezone().isoformat(), exit_code=code)
    LOCK.write_text(json.dumps(lease))


def run(exe, args):
    out = subprocess.run(
        [exe, "--bench", "--json", *args], check=True, text=True, capture_output=True
    ).stdout
    return {r["name"]: r for r in map(json.loads, out.splitlines())}


def pct(new, old):
    return f"{(new - old) / old * 100:+.2f}%" if old else "-"


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("base", nargs="?", default="HEAD")
    p.add_argument("filter", nargs="?")
    p.add_argument("--reps", type=int)
    p.add_argument("--rounds", type=int, default=2, help="A B B A blocks (default 2)")
    a = p.parse_args()

    sha, tree = base_tree(a.base)
    print(f"building base {sha[:12]} and the working tree", file=sys.stderr)
    exes = {"A": build(tree), "B": build(ROOT)}
    args = ["--suite", str(ROOT / "benches" / "suite.toml")]
    args += [a.filter] if a.filter else []
    args += ["--reps", str(a.reps)] if a.reps else []

    order = "ABBA" * a.rounds
    runs = {"A": [], "B": []}
    lease, code = acquire(), 1
    try:
        for i, side in enumerate(order):
            print(f"run {i + 1}/{len(order)}: {side}", file=sys.stderr)
            runs[side].append(run(exes[side], args))
        code = 0
    finally:
        release(lease, code)

    print(f"{'bench':<34} {'instr':>9} {'wall':>9} {'noise':>9}  arena")
    for name in runs["A"][-1]:
        a_, b_ = ([r[name] for r in runs[k] if name in r] for k in "AB")
        base, best = (min(x, key=lambda r: r["wall_ms"]) for x in (a_, b_))
        walls = [r["wall_ms"] for r in a_]
        noise = (max(walls) - min(walls)) / min(walls) * 100 if min(walls) else 0
        arena = (
            "="
            if all(r["arena"] == base["arena"] for r in b_)
            else pct(best["arena"], base["arena"])
        )
        fail = (
            f"  fail {base['failed']} -> {best['failed']}"
            if best["failed"] != base["failed"]
            else ""
        )
        instr = pct(
            min(r["instructions"] for r in b_), min(r["instructions"] for r in a_)
        )
        print(
            f"{name:<34} {instr:>9} {pct(best['wall_ms'], base['wall_ms']):>9} {noise:>8.2f}%  {arena}{fail}"
        )


if __name__ == "__main__":
    main()
