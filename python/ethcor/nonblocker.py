"""A3′: Nonblocker in poly(n)·2^{εk}: Ore's bound, then dominating sets on fewer than 2k vertices.

Lean: `EthCor.Nb.niL`, `subM`, `core`, `nb_answer` (lean/EthCor/Nonblocker.lean); `EthCor.NbTM.nX`,
`mX`, `kX`, `jX`, `preN`, `postN`, `nbM`, theorem `EthCor.NbTM.nb_fpt` (NonblockerTM.lean). The counter
is Anthropic's `FromPrinted.Consequences.DOMcount`, which returns the number of dominating sets of
size s of the graph coded by `codeWith G s` = 1^n 0 1^s 0 matrix. It equals `cntS n s (domF n m)`
(Anthropic's `GraphProblems.stDom`), which is what `dom_count` computes here; Anthropic's machine
first cuts the unbounded-width clauses of `domF` with its shortening tree.

Algorithm: n′ := number of vertices with a neighbour. If 2k ≤ n′ answer yes (Ore). If n′ < k answer
no. Otherwise count the dominating sets of size n′ − k of the graph induced on these vertices
(n′ < 2k vertices) and answer whether the count is positive.
"""

from __future__ import annotations

from .cnf import Fml, count_sized
from .graphs import Matrix, adjB, code, unary
from .lists import ones, rest


def niL(n: int, m: list[bool]) -> list[int]:
    """The vertices with a neighbour (Lean: `niL`)."""
    return [v for v in range(n) if any(adjB(n, m, v, u) for u in range(n))]


def subM(n: int, m: list[bool], J: list[int]) -> list[bool]:
    """The matrix of the graph induced on J (Lean: `subM`)."""
    return [adjB(n, m, u, v) for u in J for v in J]


def preN(x: list[bool]) -> list[bool]:
    """The front end on code G ++ unary k (Lean: `preN`); its output is a word codeWith H s."""
    n = ones(x)
    r = rest(x)
    m = r[: n * n]
    k = ones(r[n * n:])
    J = niL(n, m)
    if 2 * k <= len(J):
        return [False, False]  # codeWith (⊥ on 0 vertices) 0: one dominating set
    if len(J) < k:
        return [True, False, False, False]  # codeWith (⊥ on 1 vertex) 0: none
    return unary(len(J)) + unary(len(J) - k) + subM(n, m, J)


def domF(n: int, m: list[bool]) -> Fml:
    """Anthropic's `GraphProblems.domF`: for every v the clause x_v ∨ ⋁_{u ∈ N(v)} x_u."""
    return [[(u, True) for u in [v] + [u for u in range(n) if u != v and adjB(n, m, v, u)]] for v in range(n)]


def dom_count(w: list[bool]) -> int:
    """What `DOMcount` returns on the word codeWith G s: the number of dominating sets of size s."""
    n = ones(w)
    r = rest(w)
    s = ones(r)
    m = rest(r)
    return count_sized(domF(n, m), n, s)


def nb_word(x: list[bool]) -> bool:
    """The machine `nbM`: front end, counter, `postN` (is the count positive)."""
    return 0 < dom_count(preN(x))


def has_nonblocker(adj: Matrix, k: int) -> bool:
    """Whether G has a dominating set with at most n − k vertices, by the algorithm."""
    return nb_word(code(adj) + unary(k))
