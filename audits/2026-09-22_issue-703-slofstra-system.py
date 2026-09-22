#!/usr/bin/env python3
"""Specify the finite binary system used in the issue-703 mathematical audit.

Source: Slofstra, arXiv:1703.08618v2, Proposition 5.1, Proposition 4.8,
Lemma 4.4, and equation (4.1). The accompanying audit explains the seed.
This checks finite bookkeeping, not quantum nonattainment. With --json it
prints every column name and row of Ax=b, using zero-based column indices.
"""

import argparse
import json
from fractions import Fraction


def binary_system():
    """Apply the two finite presentation constructions to the fixed seed."""
    seed = ["a", "b", "c", "z", "w", "d", "e", "W", "z2", "w2",
            "r", "s", "t", "Z"]
    conjugacies = [
        ("w", "a", "d"), ("z", "d", "a"),
        ("w", "b", "e"), ("z", "e", "c"),
        ("w", "z", "W"),
        ("w2", "w", "r"), ("z2", "r", "W"),
        ("w2", "z", "s"), ("z2", "s", "z"),
        ("t", "a", "Z"),
    ]
    columns = list(seed)
    rows = [(["a", "b", "c"], 0), (["a", "Z"], 1)]
    nice_conjugacies = []

    # Lemma 4.4: replace the original conjugacies by a nice presentation.
    for u in seed:
        columns.extend([f"y:{u}", f"z:{u}", f"w:{u}"])
    columns.append("f")
    for u in seed:
        rows.extend([([u, f"y:{u}", f"z:{u}"], 0),
                     ([u, "f", f"w:{u}"], 0)])
        nice_conjugacies.append(("f", f"y:{u}", f"z:{u}"))
    for k, (u, v, w) in enumerate(conjugacies):
        g = f"g:{k}"
        columns.append(g)
        rows.append(([g, f"y:{v}", f"z:{w}"], 0))
        nice_conjugacies.append((f"w:{u}", f"y:{v}", f"z:{w}"))
    assert (len(columns), len(rows), len(nice_conjugacies)) == (67, 40, 24)
    for _, v, w in nice_conjugacies:
        assert any(v in support and w in support for support, _ in rows)

    # Proposition 4.2, equation (4.1): six binary rows per conjugacy.
    for k, (u, v, w) in enumerate(nice_conjugacies):
        h = [f"h:{k}:{j}" for j in range(1, 8)]
        columns.extend(h)
        rows.extend((support, 0) for support in [
            [u, h[0], h[1]], [v, h[1], h[2]], [h[2], h[3], h[4]],
            [u, h[4], h[5]], [w, h[5], h[6]], [h[0], h[3], h[6]],
        ])
    assert len(columns) == len(set(columns)) == 235
    assert len(rows) == 184
    index = {name: i for i, name in enumerate(columns)}
    indexed = []
    for support, rhs in rows:
        assert len(support) == len(set(support))
        indexed.append({"support": sorted(index[u] for u in support), "rhs": rhs})
    assert sorted(len(row["support"]) for row in indexed) == [2] + [3] * 183
    assert sum(row["rhs"] for row in indexed) == 1
    return {"source": "https://arxiv.org/pdf/1703.08618v2",
            "columns": columns, "rows": indexed}


def gf2_rank(vectors):
    """Compute the rank of binary rows represented by integer bitmasks."""
    basis = {}
    for vector in vectors:
        while vector:
            pivot = vector.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = vector
                break
            vector ^= basis[pivot]
    return len(basis)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="print the complete finite system")
    args = parser.parse_args()
    system = binary_system()
    rows = system["rows"]
    masks = [sum(1 << j for j in row["support"]) for row in rows]
    augmented = [mask | (row["rhs"] << 235) for mask, row in zip(masks, rows)]
    ranks = gf2_rank(masks), gf2_rank(augmented)
    assert ranks[1] == ranks[0] + 1
    mass = Fraction(1, 2 * 184 * 235)
    assert 2 * 184 * 235 * mass == 1
    if args.json:
        print(json.dumps(system, indent=2))
    else:
        print("184 equations; 235 variables; row sizes 2 (once), 3 (183 times)")
        print(f"GF(2) ranks: A={ranks[0]}, [A|b]={ranks[1]} (no classical solution)")
        print(f"Symmetric game: 419 questions; 16 answers; supported-pair mass {mass}")
        print("Quantum value/nonattainment: external theorem plus mathematical argument,")
        print("not established by this finite calculation.")


if __name__ == "__main__":
    main()
