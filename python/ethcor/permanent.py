"""N6: the permanent of 0/1 matrices, and of {−1, 0, 1} matrices, in poly(n)·2^{εm}.

Lean: `EthCor.Perm.ents`, `clash`, `permF`, `cntS_permF`, `permanent_eq` (lean/EthCor/Perm.lean);
`EthCor.PermTM.leafP`, `permM`, theorem `EthCor.PermTM.perm_fpt` (PermTM.lean). The signed version
mirrors `EthCor.SPerm.xorC`, `compC`, `chainF`, `sF`, `negs`, `numPar`, `cnt_sperm`, `permanent_signed`
(SignedPerm.lean) and `EthCor.SPermTM.leafS`, `spermM`, theorem `EthCor.SPermTM.sperm_fpt`
(SignedPermTM.lean).

Algorithm (0/1): one variable per one of A; for every two ones in the same row or column the clause
¬x_a ∨ ¬x_b; count the solutions with exactly n true variables with Anthropic's `SIZED` (width 2, m
variables). If m < n the permanent is 0.

Algorithm ({−1, 0, 1}): add z = 0, a parity chain p_k = p_{k−1} ⊕ x_{g k} over the r entries that are
−1, complements q_k = ¬p_k and p_{r−1} = b; count the solutions with n + r true variables for
b = 0 and b = 1 (`SIZED`, width 3, m + 1 + 2r variables); the permanent is the first count minus
the second.
"""

from __future__ import annotations

from .cnf import Fml, count_sized
from .graphs import Matrix, adjB, matrix, pairs, unary
from .lists import ones, rest


def ents(n: int, mA: list[bool]) -> list[tuple[int, int]]:
    """The nonzero entries (row, column), row by row (Lean: `ents`)."""
    return [p for p in pairs(n) if adjB(n, mA, p[0], p[1])]


def clash(p: tuple[int, int], q: tuple[int, int]) -> bool:
    return p[0] == q[0] or p[1] == q[1]


def permF(E: list[tuple[int, int]]) -> Fml:
    """No two chosen entries in a row or column (Lean: `permF`)."""
    return [[(a, False), (b, False)] for (a, b) in pairs(len(E)) if a < b and clash(E[a], E[b])]


def perm_word(x: list[bool]) -> int:
    """The machine `permM` on the word unary n ++ hmat A: `leafP`, then the sized counter."""
    n = ones(x)
    E = ents(n, rest(x))
    if n <= len(E):
        return count_sized(permF(E), len(E), n)
    return count_sized([[]], 0, 0)


def permanent01(A: Matrix) -> int:
    """The permanent of the 0/1 matrix A, by the algorithm."""
    return perm_word(unary(len(A)) + matrix(A))


# --- {−1, 0, 1} matrices: the parity chain of SignedPerm.lean


def xorC(c: int, a: int, x: int) -> Fml:
    """c = a ⊕ x (Lean: `SPerm.xorC`)."""
    return [[(c, False), (a, True), (x, True)], [(c, False), (a, False), (x, False)],
            [(c, True), (a, False), (x, True)], [(c, True), (a, True), (x, False)]]


def compC(p: int, q: int) -> Fml:
    """q = ¬p (Lean: `SPerm.compC`)."""
    return [[(p, True), (q, True)], [(p, False), (q, False)]]


def chainF(m: int, g: list[int], b: bool) -> Fml:
    """z = x_m false, p_k = x_{m+1+k} = p_{k−1} ⊕ x_{g k}, q_k = x_{m+1+r+k} = ¬p_k, p_{r−1} = b."""
    r = len(g)
    F: Fml = [[(m, False)]]
    for k in range(r):
        F += xorC(m + 1 + k, m + k, g[k])
    for k in range(r):
        F += compC(m + 1 + k, m + 1 + r + k)
    F.append([(m + r, b)])
    return F


def sF(E: list[tuple[int, int]], g: list[int], b: bool) -> Fml:
    return permF(E) + chainF(len(E), g, b)


def negs(n: int, mS: list[bool], E: list[tuple[int, int]]) -> list[int]:
    """The indices of the entries of E that are −1 (Lean: `SPerm.negs`)."""
    return [t for t in range(len(E)) if adjB(n, mS, E[t][0], E[t][1])]


def num_parity(A: Matrix, Sg: Matrix, b: bool) -> int:
    """The permutations along nonzero entries with an even (b = False) or odd (b = True) number of
    −1 entries, as the sized count of `sF` with n + r true variables."""
    n = len(A)
    E = ents(n, matrix(A))
    g = negs(n, matrix(Sg), E)
    if n > len(E):
        return 0
    return count_sized(sF(E, g, b), len(E) + 1 + 2 * len(g), n + len(g))


def permanent_signed(A: Matrix, Sg: Matrix) -> int:
    """The permanent of the matrix with entries −1 (A and Sg), 1 (A, not Sg) and 0 (not A)."""
    return num_parity(A, Sg, False) - num_parity(A, Sg, True)


def leafP(x: list[bool]) -> tuple[int, int, Fml]:
    """The counter's input on unary n ++ hmat A (Lean: `EthCor.PermTM.leafP`)."""
    n = ones(x)
    E = ents(n, rest(x))
    if n <= len(E):
        return len(E), n, permF(E)
    return 0, 0, [[]]


def leafS(x: list[bool]) -> tuple[int, int, Fml]:
    """The counter's input on b :: (unary n ++ hmat A ++ hmat S) (Lean: `EthCor.SPermTM.leafS`)."""
    b = x[0] if x else False
    y = list(x[1:])
    n = ones(y)
    r = rest(y)
    E = ents(n, r[: n * n])
    g = negs(n, r[n * n:], E)
    if n <= len(E):
        return len(E) + 1 + len(g) + len(g), n + len(g), sF(E, g, b)
    return 0, 0, [[]]
