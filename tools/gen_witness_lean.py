#!/usr/bin/env python3
"""Emit chunked Lean list-literal definitions from a witness-chain data file.

The input (tools/witness_a17.lean.txt etc.) is one `--` comment header line followed by
comma-separated natural numbers with arbitrary line breaks.  The output (stdout) is a block
of Lean definitions

    private def w<TAG>_0 : List N := [ ... ]        -- <= CHUNK entries each
    ...
    def witnessList<TAG> : List N := w<TAG>_0 ++ w<TAG>_1 ++ ...

Chunking keeps each list literal shallow (list literals elaborate as nested `cons`, and a
single multi-thousand-element literal can exceed the elaborator recursion depth).

Usage: python tools/gen_witness_lean.py <datafile> <tag> [chunk_size=300]
"""
import sys

WIDTH = 98
NAT = "ℕ"  # the Lean natural-number glyph


def wrap(prefix: str, items: list, open_b: str, close_b: str, sep: str, indent: str) -> str:
    """Render `prefix` + open_b + sep.join(items) + close_b, wrapped at WIDTH columns."""
    lines = []
    cur = prefix + open_b
    for i, it in enumerate(items):
        tok = str(it) + (sep if i + 1 < len(items) else close_b)
        if len(cur) + len(tok) > WIDTH:
            lines.append(cur.rstrip())
            cur = indent + tok
        else:
            cur += tok
    lines.append(cur.rstrip())
    return "\n".join(lines)


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")  # the Lean output is UTF-8 regardless of console codepage
    path, tag = sys.argv[1], sys.argv[2]
    chunk = int(sys.argv[3]) if len(sys.argv) > 3 else 300
    nums = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("--"):
                continue
            nums.extend(int(tok) for tok in line.split(",") if tok.strip())
    assert nums == sorted(nums) and len(set(nums)) == len(nums), "witness data must be sorted"
    chunks = [nums[i:i + chunk] for i in range(0, len(nums), chunk)]
    names = [f"w{tag}_{i}" for i in range(len(chunks))]
    out = []
    for name, ch in zip(names, chunks):
        out.append(wrap(f"private def {name} : List {NAT} := ", ch, "[", "]", ", ", "  "))
    out.append("")
    out.append(f"/-- The verified witness chain at scale `A = {tag}` ({len(nums)} clean residues). -/")
    out.append(wrap(f"def witnessList{tag} : List {NAT} :=\n  ", names, "", "", " ++ ", "    "))
    print("\n".join(out))


if __name__ == "__main__":
    main()
