"""A2 and N5: k-colorings and homomorphisms G → H, images written in binary.

Lean: `EthCor.colB`, `EthCor.nb`, `EthCor.forbid` (lean/EthCor/ColorFormula.lean), the front end
`EthCor.preC` (ColorTM.lean), theorem `EthCor.colorings_subexp`; `EthCor.Hom.homB`, `EthCor.Hom.hmat`,
`EthCor.Hom.preHom` (HomFormula.lean, HomTM.lean), theorem `EthCor.Hom.hom_subexp`.

Algorithm (both): write the CNF on n·b + 4 variables, b = ⌈log₂ k⌉, and count its satisfying
assignments with the counter of the Main Theorem (Anthropic's uniform #k-SAT machine, width 2b).
"""

from __future__ import annotations

from .cnf import Fml, count
from .graphs import Matrix, adjB, code, matrix, pairs, unary
from .lists import log2, ones, rest, test_bit


def nb(k: int) -> int:
    """Bits per vertex: ⌊log₂(2(k−1))⌋, which is ⌈log₂ k⌉ for k ≥ 2 (Lean: `nb`)."""
    return log2(2 * max(k - 1, 0))


def forbid(b: int, v: int, c: int) -> list[tuple[int, bool]]:
    """The clause «the b bits of vertex v do not spell c» (Lean: `forbid`)."""
    return [(v * b + j, not test_bit(c, j)) for j in range(b)]


def _common(k: int, n: int) -> tuple[Fml, Fml, Fml]:
    b = nb(k)
    invalid = [forbid(b, v, c) for v in range(n) for c in range(2 * k) if k <= c and log2(c) < b]
    taut = [[(i, True), (i, False)] for i in range(n * b)]
    pad = [[(n * b + i, True)] for i in range(4)]
    return invalid, taut, pad


def colB(k: int, n: int, m: list[bool]) -> Fml:
    """The CNF of the proper k-colorings of the graph with matrix m (Lean: `colB k n m`)."""
    b = nb(k)
    invalid, taut, pad = _common(k, n)
    edge = [forbid(b, p[0], c) + forbid(b, p[1], c) for p in pairs(n) if adjB(n, m, p[0], p[1]) for c in range(k)]
    return invalid + edge + taut + pad


def homB(h: int, n: int, mH: list[bool], m: list[bool]) -> Fml:
    """The CNF of the homomorphisms to the relation with matrix mH (Lean: `Hom.homB h n mH m`)."""
    b = nb(h)
    invalid, taut, pad = _common(h, n)
    edge = [forbid(b, p[0], q[0]) + forbid(b, p[1], q[1])
            for p in pairs(n) if adjB(n, m, p[0], p[1])
            for q in pairs(h) if not adjB(h, mH, q[0], q[1])]
    return invalid + edge + taut + pad


def colorings_word(x: list[bool]) -> int:
    """The machine of `colorings_uniform` on the word unary k ++ code G (for 2 ≤ k ≤ n): the front end
    `preC` reads k and G, writes `colB`, and the counter counts it."""
    k = ones(x)
    g = rest(x)
    n = ones(g)
    m = rest(g)
    return count(colB(k, n, m), n * nb(k) + 4)


def num_colorings(adj: Matrix, k: int) -> int:
    """The number of proper k-colorings of G, by the algorithm (k ≥ 2)."""
    return colorings_word(unary(k) + code(adj))


def hom_word(x: list[bool]) -> int:
    """The machine of `hom_uniform` on the word unary h ++ hmat H ++ code G (for 2 ≤ h ≤ n)."""
    h = ones(x)
    r = rest(x)
    mH = r[: h * h]
    g = r[h * h:]
    n = ones(g)
    m = rest(g)
    return count(homB(h, n, mH, m), n * nb(h) + 4)


def num_hom(adj: Matrix, H: Matrix) -> int:
    """The number of maps f : V(G) → [h] with H(f(u), f(v)) for every edge uv, by the algorithm."""
    return hom_word(unary(len(H)) + matrix(H) + code(adj))
