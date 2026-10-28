"""Graphs and input words as in the Lean development.

A graph on the vertices 0..n-1 is given by its n × n adjacency matrix (`adj[u][v]`, symmetric, no
loops). Its word is `code(G)` = 1^n 0 followed by the n² matrix entries row by row (Lean:
`GraphProblems.code`, `GraphProblems.matrix`). `adjB`, `pairs` and `edges` are the list functions
the Lean front ends use to read the matrix.
"""

from __future__ import annotations

import random
from typing import Sequence

Matrix = list[list[bool]]


def unary(m: int) -> list[bool]:
    """1^m 0 (Lean: `unary`)."""
    return [True] * m + [False]


def matrix(adj: Matrix) -> list[bool]:
    """The n² entries row by row (Lean: `matrix G`, and `Hom.hmat` for a relation)."""
    return [bool(b) for row in adj for b in row]


def code(adj: Matrix) -> list[bool]:
    """1^n 0, then the matrix (Lean: `code G`)."""
    return unary(len(adj)) + matrix(adj)


def adjB(n: int, m: Sequence[bool], u: int, v: int) -> bool:
    """Entry u·n + v of the matrix word m, False beyond it (Lean: `adjB`)."""
    i = u * n + v
    return bool(m[i]) if 0 <= i < len(m) else False


def pairs(n: int) -> list[tuple[int, int]]:
    """range n × range n, in lexicographic order (Lean: `GraphProblems.pairs`)."""
    return [(a, b) for a in range(n) for b in range(n)]


def edges(n: int, m: Sequence[bool]) -> list[tuple[int, int]]:
    """The edges (u, v), u < v, in lexicographic order (Lean: `EthCor.Ham.edges`)."""
    return [(u, v) for (u, v) in pairs(n) if u < v and adjB(n, m, u, v)]


def random_graph(n: int, p: float, rng: random.Random) -> Matrix:
    adj = [[False] * n for _ in range(n)]
    for u in range(n):
        for v in range(u + 1, n):
            if rng.random() < p:
                adj[u][v] = adj[v][u] = True
    return adj


def random_relation(h: int, p: float, rng: random.Random) -> Matrix:
    """A relation on 0..h-1 (loops allowed, not necessarily symmetric)."""
    return [[rng.random() < p for _ in range(h)] for _ in range(h)]


def edge_list(adj: Matrix) -> list[tuple[int, int]]:
    n = len(adj)
    return [(u, v) for u in range(n) for v in range(u + 1, n) if adj[u][v]]
