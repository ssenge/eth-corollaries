"""A6: odd cycle transversal, deterministic, any density.

The input is `code G ++ unary s` with s = n − k; the front end `preO` writes `octF n E = sideF n ++
edgeOC n E` on 3n variables (a kept bit x_v, a color bit c_v = x_{n+v} and its complement at 2n + v;
c_u ≠ c_v on the edges between kept vertices) with the target n + s; Anthropic's `SIZED` counts the
solutions of that size, and `postO` says whether the count is positive. It is positive iff some s
vertices induce a bipartite subgraph (`OctTM.oct_pos`), i.e. iff G has an odd cycle transversal with
at most k vertices (`OctTM.oct_iff`, `OctTM.oct_tm`; lean/EthCor/OctTM.lean).
"""

from __future__ import annotations

from itertools import combinations
from typing import Sequence

from .cnf import Fml
from .connected import _sized, lC, sideF
from .graphs import Matrix, code, unary
from .hamcycle import EH, Edges, nH


def edgeOC(n: int, E: Edges) -> Fml:
    """c_u ≠ c_v on the edges between kept vertices (Lean: `OctTM.edgeOC`)."""
    return [C for a, b in E for C in
            ([(a, False), (b, False), (n + a, True), (n + b, True)],
             [(a, False), (b, False), (n + a, False), (n + b, False)])]


def octF(n: int, E: Edges) -> Fml:
    """Lean: `OctTM.octF n E = sideF n ++ edgeOC n E`, on 3n variables."""
    return sideF(n) + edgeOC(n, E)


def preO(x: Sequence[bool]) -> tuple[int, int, Fml]:
    """The front end of `oct_tm` (Lean: `OctTM.preO`)."""
    n = nH(x)
    return (n + n + n, n + lC(x), octF(n, EH(x)))


def oct_word(x: Sequence[bool]) -> list[bool]:
    """The machine `octM`: `preO`, `SIZED`, `postO`."""
    return [_sized(preO(x)) > 0]


def oct_decide(adj: Matrix, k: int) -> bool:
    """A6: whether G has an odd cycle transversal with at most k vertices, on the input
    `code G ++ unary (n − k)` (Lean: `EthCor.OctTM.oct_tm`)."""
    return oct_word(code(adj) + unary(len(adj) - k))[0]


def bipartite_in(adj: Matrix, Y: Sequence[int]) -> bool:
    """G[Y] has a proper 2-coloring (breadth-first search)."""
    Y = list(Y)
    col: dict[int, int] = {}
    for r in Y:
        if r in col:
            continue
        col[r], todo = 0, [r]
        while todo:
            u = todo.pop()
            for v in Y:
                if adj[u][v]:
                    if v not in col:
                        col[v] = 1 - col[u]
                        todo.append(v)
                    elif col[v] == col[u]:
                        return False
    return True


def min_oct(adj: Matrix) -> int:
    """The minimum odd cycle transversal by brute force."""
    n = len(adj)
    return next(k for k in range(n + 1) for X in combinations(range(n), k)
                if bipartite_in(adj, [v for v in range(n) if v not in X]))
