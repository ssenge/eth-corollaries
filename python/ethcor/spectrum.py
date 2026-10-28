"""A4: the Max-SAT spectrum of a sparse CNF in C·2^{δn}.

Lean: `EthCor.Spectrum.xl`, `yC`, `specF`, `preS`, `specM`, theorems `cntS_specF`,
`maxsat_spectrum` (lean/EthCor/Spectrum.lean); `EthCor.CnfTree.pairF` (CnfTree.lean). The input is
`unary t ++ SatFree.enc φ`, read with `GraphProblems.ones`, `rest` and `FreeCode.readFree`; the
counter is Anthropic's `FromPrinted.Consequences.SIZED` (width r + 2).

Algorithm: on 2n + m variables, x_{2u+1} = ¬x_{2u} (the pair clauses), and for the j-th clause C
the variable y_j = x_{2n+j} with y_j ↔ C, the literal (u, b) of C read on x_{2u}. The solutions are
the assignments of φ, with n + (number of satisfied clauses) true variables; the number with n + t
true variables is the number of assignments satisfying exactly t clauses.
"""

from __future__ import annotations

from typing import Sequence

from .cnf import Clause, Fml
from .cnf_anywidth import enc, ones, pairF, readFree, rest, sized
from .graphs import unary


def xl(l: tuple[int, bool]) -> tuple[int, bool]:
    """The literal (u, b) on the variable 2u (Lean: `xl`)."""
    return (2 * l[0], l[1])


def yC(n: int, j: int, C: Clause) -> Fml:
    """y ↔ C for y = x_{2n+j}: ¬y ∨ C, and ¬l ∨ y for every literal l of C (Lean: `yC`)."""
    return [[(2 * n + j, False)] + [xl(l) for l in C]] + [[(2 * l[0], not l[1]), (2 * n + j, True)] for l in C]


def specF(n: int, psi: Fml) -> Fml:
    """The pair clauses and y_j ↔ C_j for every clause C_j of ψ (Lean: `specF`)."""
    return pairF(n) + [D for j in range(len(psi)) for D in yC(n, j, psi[j])]


def preS(x: Sequence[bool]) -> tuple[int, int, Fml]:
    """Read t in unary and the code of φ; (2n + m, n + t, `specF`) (Lean: `preS`)."""
    n, psi = readFree(rest(x))
    return (2 * n + len(psi), n + ones(x), specF(n, psi))


def spec_word(x: Sequence[bool]) -> int:
    """The machine `specM` on a word: `preS`, then `SIZED` (Lean writes the result with `Nat.bits`)."""
    return sized(preS(x))


def maxsat_spectrum(F: Fml, n: int, t: int) -> int:
    """`specM` on `unary t ++ SatFree.enc F`: the number of assignments of n variables that satisfy
    exactly t clauses of F (`maxsat_spectrum`; 0 for t beyond the number of clauses)."""
    return spec_word(unary(t) + enc(F, n))
