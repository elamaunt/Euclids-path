#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Emit chunked Lean list-literal definitions for grave-depth path witnesses.

Input: a JSON file (produced by `grave_depth_harness.py emit`) holding one entry per
center m = 1, 2, ... (POSITIONAL): entry i is the min-depth peel path for m = i + 1 as a
list of steps [t, p, e, d] with

    t = peel target, p = peeled prime (>= 5),
    e = side_is_minus   (True: wing 6m - 1, i.e. eps = +1 in PeelStep's 6m - eps),
    d = target_is_plus  (True: cofactor 6t + 1, i.e. delta = +1 in p * (6t + delta)),

and an EMPTY list when m itself is a twin center.  Every step is INDEPENDENTLY re-verified
here (pure trial division, no shared code with the harness) before anything is emitted:

    (6m - 1 if e else 6m + 1) == p * (6t + 1 if d else 6t - 1),  p prime >= 5,  1 <= t < m,

the path chains (next step starts at the previous target), the terminal center is a twin
(both wings prime) and the path length is <= 3.

Output (stdout): Lean chunk definitions in the `gen_witness_lean.py` house pattern

    private def gd_0 : List (List (N x N x Bool x Bool)) := [...]   -- <= CHUNK entries
    ...
    def depthData : List (List (N x N x Bool x Bool)) := gd_0 ++ gd_1 ++ ...

Usage: python tools/gen_paths_lean.py <paths.json> [chunk_size=200]
"""
import json
import math
import sys

WIDTH = 98
TUP = "ℕ × ℕ × Bool × Bool"


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for q in range(2, math.isqrt(n) + 1):
        if n % q == 0:
            return False
    return True


def verify(data) -> None:
    for i, steps in enumerate(data):
        m = i + 1
        assert len(steps) <= 3, (m, len(steps))
        cur = m
        for (t, p, e, d) in steps:
            assert 1 <= t < cur, (m, cur, t)
            assert p >= 5 and is_prime(p), (m, p)
            side = 6 * cur - 1 if e else 6 * cur + 1
            cof = 6 * t + 1 if d else 6 * t - 1
            assert side == p * cof, (m, cur, t, p, e, d)
            cur = t
        assert is_prime(6 * cur - 1) and is_prime(6 * cur + 1), (m, cur)


def render(steps) -> str:
    return "[" + ", ".join(
        "(%d, %d, %s, %s)" % (t, p, str(bool(e)).lower(), str(bool(d)).lower())
        for (t, p, e, d) in steps) + "]"


def wrap(prefix: str, items, close: str, indent: str, sep: str = ", ") -> str:
    lines, cur = [], prefix
    for i, it in enumerate(items):
        tok = it + (sep if i + 1 < len(items) else close)
        if len(cur) + len(tok) > WIDTH:
            lines.append(cur.rstrip())
            cur = indent + tok
        else:
            cur += tok
    lines.append(cur.rstrip())
    return "\n".join(lines)


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    path = sys.argv[1]
    chunk = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    with open(path, encoding="utf-8") as f:
        data = json.load(f)
    verify(data)
    chunks = [data[i:i + chunk] for i in range(0, len(data), chunk)]
    names = ["gd_%d" % i for i in range(len(chunks))]
    out = []
    for name, ch in zip(names, chunks):
        out.append(wrap("private def %s : List (List (%s)) := [" % (name, TUP),
                        [render(s) for s in ch], "]", "  "))
    out.append("")
    out.append("/-- Positional min-depth path data: entry `i` is the verified peel path for the center")
    out.append("    `m = i + 1` (empty list = `m` is itself a twin center); %d entries, every step" % len(data))
    out.append("    re-verified arithmetically at emission (`tools/gen_paths_lean.py`). -/")
    out.append(wrap("def depthData : List (List (%s)) :=\n  " % TUP, names, "", "    ", sep=" ++ "))
    print("\n".join(out))


if __name__ == "__main__":
    main()
