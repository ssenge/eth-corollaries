"""A3: Vertex Cover in poly(n)·2^{εk}, by degree branching and sized counting at the leaves.

Lean: `EthCor.Vc.nbs`, `cand`, `pick`, `delV`, `delN`, `stepV`, `verts`, `vcClauses`, `leafV`
(lean/EthCor/VcTree.lean); `EthCor.VcTM.rootV`, `postV`, `vcM`, theorem `EthCor.VcTM.vc_fpt`
(VcTM.lean).

Algorithm, for a degree d chosen from ε ((2/d)·lg(e·d) ≤ ε/4, `CnfTree.exists_width`):
  node (k', E): while k' > 0 and some endpoint v has ≥ d distinct neighbours, branch into
  (k'−1, E∖v) and (k'−|N(v)|, E∖N[v]); at a leaf with |V(E)| ≤ k'·d count the vertex covers of
  size min(k', |V(E)|) of E with Anthropic's `SIZED` (width 2, at most k·d variables); answer
  whether the sum over the leaves is positive.
"""

from __future__ import annotations

import math

from .cnf import Fml, count_sized
from .graphs import Matrix, code, edges, unary
from .lists import dedup, idx_of, ones, rest

Edge = tuple[int, int]
Node = tuple[int, list[Edge]]


def nbs(E: list[Edge], v: int) -> list[int]:
    """The distinct neighbours of v (Lean: `nbs`)."""
    return dedup([e[1] if e[0] == v else e[0] for e in E if e[0] == v or e[1] == v])


def cand(E: list[Edge]) -> list[int]:
    """The ends of the edges, in order (Lean: `cand`)."""
    return [u for e in E for u in e]


def pick(d: int, x: Node) -> int | None:
    """The first endpoint with at least d neighbours, if the budget is positive (Lean: `pick`)."""
    for v in cand(x[1]):
        if 0 < x[0] and d <= len(nbs(x[1], v)):
            return v
    return None


def delV(E: list[Edge], v: int) -> list[Edge]:
    return [e for e in E if not (e[0] == v or e[1] == v)]


def delN(E: list[Edge], v: int, k: int) -> list[Edge]:
    N = nbs(E, v)
    return [e for e in E if k < len(N) or not (e[0] == v or e[1] == v or e[0] in N or e[1] in N)]


def stepV(d: int, x: Node) -> tuple[Node, Node] | None:
    """The branching step (Lean: `stepV`); ℕ subtraction truncates at 0."""
    v = pick(d, x)
    if v is None:
        return None
    k, E = x
    return (max(k - 1, 0), delV(E, v)), (max(k - len(nbs(E, v)), 0), delN(E, v, k))


def leaves(d: int, x: Node) -> list[Node]:
    """The leaves of the tree below x (Lean: `leaves (stepV d) (k + d)`, all final by `leaves_final`)."""
    s = stepV(d, x)
    if s is None:
        return [x]
    return leaves(d, s[0]) + leaves(d, s[1])


def verts(E: list[Edge]) -> list[int]:
    return dedup(cand(E))


def vcClauses(E: list[Edge]) -> Fml:
    V = verts(E)
    return [[(idx_of(e[0], V), True), (idx_of(e[1], V), True)] for e in E]


def leafV(d: int, x: Node) -> tuple[int, int, Fml]:
    """The counter's input at a leaf: (number of variables, size, formula) (Lean: `leafV`)."""
    k, E = x
    V = verts(E)
    if k * d < len(V):
        return 0, 0, [[]]
    return len(V), min(k, len(V)), vcClauses(E)


def rootV(x: list[bool]) -> Node:
    """Read code G ++ unary k (Lean: `rootV`)."""
    n = ones(x)
    r = rest(x)
    return ones(r[n * n:]), edges(n, r[: n * n])


def vc_word(x: list[bool], d: int) -> bool:
    """The machine `vcM` on the word code G ++ unary k: walk, count at the leaves, sum, sign."""
    total = 0
    for y in leaves(d, rootV(x)):
        N, s, F = leafV(d, y)
        total += count_sized(F, N, s)
    return 0 < total


def degree_for(eps: float) -> int:
    """The least d ≥ 2 with (2/d)·lg(e·d) ≤ ε/4, the condition of `CnfTree.exists_width 1`."""
    d = 2
    while (2 / d) * math.log2(math.e * d) > eps / 4:
        d += 1
    return d


def has_vertex_cover(adj: Matrix, k: int, d: int = 3) -> bool:
    """Whether G has a vertex cover with at most k vertices, by the algorithm with degree d ≥ 1."""
    return vc_word(code(adj) + unary(k), d)
