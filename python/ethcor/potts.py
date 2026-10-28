"""N3: the Potts density of states of a sparse graph in C·2^{δn}, and the Tutte polynomial on the
hyperbola (x−1)(y−1) = q.

Lean: `EthCor.PottsTM.amo`, `vtxF`, `colF`, `edgeM`, `monoF`, `pottsF`, `preP`, `pottsM`, theorems
`cnt_pottsF`, `potts_spectrum`, `tutte_tm` (lean/EthCor/PottsTM.lean); `EthCor.Potts.comps`,
`tutte`, theorem `tutte_hyperbola` (Potts.lean). The input is `code G ++ unary j`, read with
`EthCor.HamTM.gH`, `nH`, `EH` and `EthCor.HamITM.sI`; the edge list is `EthCor.Ham.edges`; the
counter is Anthropic's `FromPrinted.Consequences.SIZED` (width q + 3).

Algorithm: x_{vq+c} says that the vertex v has the color c, y_i = x_{nq+i} that the i-th edge is
monochromatic. Every vertex has exactly one color, and y_i ↔ the ends of edge i have the same color.
The solutions are the colorings, with n + (number of monochromatic edges) true variables, so the
number with n + j true variables is N_j. Post-step for the Tutte polynomial: on (x−1)(y−1) = q with
x, y ≠ 1, (x−1)^{k(E)}·(y−1)^n·T(G; x, y) = Σ_j N_j·y^j.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Sequence

from .cnf import Fml
from .cnf_anywidth import ones, rest, sized
from .graphs import Matrix, code, edges, matrix, unary


def amo(q: int) -> list[tuple[int, int]]:
    """The pairs (c, c′) with c′ < c < q, in the order of range q ×ˢ range q (Lean: `amo`)."""
    return [(a, b) for a in range(q) for b in range(q) if b < a]


def vtxF(q: int, v: int) -> Fml:
    """The vertex v gets some color c < q and never two (Lean: `vtxF`)."""
    return [[(v * q + c, True) for c in range(q)]] + [[(v * q + a, False), (v * q + b, False)] for a, b in amo(q)]


def colF(n: int, q: int) -> Fml:
    """`vtxF q v` for every vertex v < n (Lean: `colF`)."""
    return [C for v in range(n) for C in vtxF(q, v)]


def edgeM(n: int, q: int, i: int, p: tuple[int, int]) -> Fml:
    """y = x_{nq+i} ↔ the edge p is monochromatic: x_{aq+c} ∧ x_{bq+c} → y, y ∧ x_{aq+c} → x_{bq+c}
    (Lean: `edgeM`)."""
    a, b = p
    y = n * q + i
    return [C for c in range(q) for C in ([(a * q + c, False), (b * q + c, False), (y, True)],
                                         [(y, False), (a * q + c, False), (b * q + c, True)])]


def monoF(n: int, q: int, E: list[tuple[int, int]]) -> Fml:
    """`edgeM` for every edge of the list (Lean: `monoF`)."""
    return [C for i in range(len(E)) for C in edgeM(n, q, i, E[i])]


def pottsF(n: int, q: int, E: list[tuple[int, int]]) -> Fml:
    """The colorings with q colors and y_i ↔ edge i monochromatic, on nq + |E| variables (Lean:
    `pottsF`)."""
    return colF(n, q) + monoF(n, q, E)


def preP(q: int, x: Sequence[bool]) -> tuple[int, int, Fml]:
    """Read code G and j in unary; (nq + m, n + j, `pottsF`) (Lean: `preP`)."""
    n = ones(x)  # nH
    m = rest(x)  # (gH x).2, the matrix and what follows it
    E = edges(n, m)  # EH
    j = ones(m[n * n:])  # ones (sI x)
    return (n * q + len(E), n + j, pottsF(n, q, E))


def potts_word(q: int, x: Sequence[bool]) -> int:
    """The machine `pottsM q` on a word: `preP q`, then `SIZED` (Lean writes it with `Nat.bits`)."""
    return sized(preP(q, x))


def potts_spectrum(adj: Matrix, q: int, j: int) -> int:
    """`pottsM q` on `code G ++ unary j`: the number of colorings with q colors and exactly j
    monochromatic edges (`potts_spectrum`, `pottsSpec G q j`)."""
    return potts_word(q, code(adj) + unary(j))


def comps(n: int, E: list[tuple[int, int]]) -> int:
    """The number of connected components of the graph on 0..n-1 with edges E (Lean: `comps`)."""
    parent = list(range(n))

    def find(a: int) -> int:
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    k = n
    for a, b in E:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb
            k -= 1
    return k


def tutte_hyperbola(adj: Matrix, q: int, y: Fraction | int) -> Fraction:
    """T(G; x, y) at x = 1 + q/(y−1), from the outputs N_j of `pottsM q` for j = 0..|E| (`tutte_tm`,
    `tutte_hyperbola`): Σ_j N_j·y^j / ((x−1)^{k(E)}·(y−1)^n)."""
    y = Fraction(y)
    if q < 1 or y == 1:
        raise ValueError("needs q ≥ 1 and y ≠ 1")
    n = len(adj)
    E = edges(n, matrix(adj))
    x = 1 + Fraction(q) / (y - 1)
    Z = sum(potts_spectrum(adj, q, j) * y**j for j in range(len(E) + 1))
    return Z / ((x - 1) ** comps(n, E) * (y - 1) ** n)
