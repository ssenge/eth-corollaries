"""A1 and A1′: counting the solutions of a CNF of any width via Anthropic's shortening tree.

Lean: `EthCor.CnfTree.lv`, `pairF`, `rootX`, theorems `cntS_rootX`, `shortens_of`
(lean/EthCor/CnfTree.lean); `EthCor.CnfTM.cnfM`, theorem `EthCor.CnfTM.cnf_counts` (CnfTM.lean);
`EthCor.GrowTree.wN`, `stepW` (GrowTree.lean); `EthCor.GrowTM.leafF`, `leafM`, `growM`, theorem
`EthCor.GrowTM.cnf_grow` (GrowTM.lean; GrowArith.lean only does arithmetic on the bounds).
Anthropic's parts: `GraphProblems.posC`, `DNode`, `stepD`, `leafD` (GraphProblems/Defs.lean, used by
GraphProblems/DomTree.lean); `Groundwork.Sparsify.leaves` (StepMachines/Math/SparsifyTree.lean);
`CountKSat.walkSum` (CountKSat/Defs.lean) with `Groundwork.Stepped.walkNext`, `walkSel`
(StepMachines/Prog/Walk.lean); the input code `SatFree.enc` (statements/KSatFreeCodeStatement.lean)
and its reader `FreeCode.readFree` (FreeCode/Reader.lean) with `Groundwork.Decode.width`, `slotDec`
(StepMachines/Prog/Decode.lean) and `Groundwork.ofWord` (StepMachines/Prog/Chunks.lean).

Algorithm (A1, `cnfM w`): read n and ψ from the word; the root has 2n variables, s = n, the clauses
of ψ as open clauses of positive literals (u, b) ↦ x_{lv(u, b)}, and the pair clauses x_{2u+1} = ¬x_{2u}
closed. While an open clause C has more than w variables, with H its first w: the light child
replaces C by H (closed), the heavy child sets H false and deletes it from all open clauses. At every
leaf Anthropic's `SIZED` counts the solutions of `leafD` with n true variables; the sum is the answer.
A1′ (`growM`) walks the same tree with the width `wN N` read off the node and counts every leaf with
the Main Theorem's machine (all solutions; the pair clauses force n true variables).

A DNode is ((N, s), (open clauses, closed formula)): Lean's `List Unit` of length N is kept as N.
"""

from __future__ import annotations

from typing import Callable, Optional, Sequence, TypeVar

from .cnf import Fml, count, count_sized

DNode = tuple[tuple[int, int], tuple[list[list[int]], Fml]]
S = TypeVar("S")
A = TypeVar("A")


# ---------------------------------------------------------------------------------------------
# list functions with Lean's semantics


def ones(x: Sequence[bool]) -> int:
    """The number of leading ones (Lean: `GraphProblems.ones`)."""
    k = 0
    while k < len(x) and x[k]:
        k += 1
    return k


def rest(x: Sequence[bool]) -> list[bool]:
    """The word after the leading ones and the zero that ends them (Lean: `GraphProblems.rest`)."""
    return list(x[ones(x) + 1:])


def log2(n: int) -> int:
    """Lean's `Nat.log2`: ⌊log₂ n⌋, and 0 for n = 0."""
    return n.bit_length() - 1 if n > 0 else 0


def dedup(l: Sequence) -> list:
    """Mathlib's `List.dedup`: drops every element that occurs again later (the last copy stays)."""
    out: list = []
    for i, a in enumerate(l):
        if a not in l[i + 1:]:
            out.append(a)
    return out


# ---------------------------------------------------------------------------------------------
# the input word


def slot(l: tuple[int, bool]) -> int:
    """A literal as a number: 2u+1 for ¬x_u, 2u+2 for x_u (Lean: `Sat3.slot`)."""
    return 2 * l[0] + 1 + int(l[1])


def encLit(n: int, l: tuple[int, bool]) -> list[bool]:
    """⌊log₂ 2n⌋ + 1 bits of the slot, low bit first (Lean: `SatFree.encLit`)."""
    return [(slot(l) >> i) & 1 == 1 for i in range(log2(2 * n) + 1)]


def encClause(n: int, C: list[tuple[int, bool]]) -> list[bool]:
    """1, then 1 and the literal for each literal, then 0 (Lean: `SatFree.encClause`)."""
    return [True] + [b for l in C for b in [True] + encLit(n, l)] + [False]


def enc(F: Fml, n: int) -> list[bool]:
    """1ⁿ 0, the clauses, 0 (Lean: `SatFree.enc` of φ : Sat3.CNF n, so every variable is below n)."""
    for C in F:
        for v, _ in C:
            if not 0 <= v < n:
                raise ValueError(f"variable {v} is not below n = {n}")
    return [True] * n + [False] + [b for C in F for b in encClause(n, C)] + [False]


def width(n: int) -> int:
    """The bits of a slot, ⌊log₂ 2n⌋ + 1 (Lean: `Groundwork.Decode.width`)."""
    return 1 if n == 0 else (2 * n).bit_length()


def ofWord(w: Sequence[bool]) -> int:
    """The number written low bit first (Lean: `Groundwork.ofWord`)."""
    return sum(1 << i for i, b in enumerate(w) if b)


def slotDec(v: int) -> Optional[tuple[int, bool]]:
    """0 = no literal, 2i+1 = ¬x_i, 2i+2 = x_i (Lean: `Groundwork.Decode.slotDec`)."""
    return None if v == 0 else ((v - 1) // 2, (v - 1) % 2 == 1)


RState = tuple[bool, bool, list[bool], list[list[bool]], list[list[list[bool]]]]


def stepR(w: int, s: RState, e: bool) -> RState:
    """One bit of the reader; the lists are last member first (Lean: `FreeCode.stepR`)."""
    p1, p2, cur, cl, acc = s
    if p1:
        if p2:
            return s
        if len(cur) + 1 == w:
            return (False, True, [], [[e] + cur] + cl, acc)
        return (True, False, [e] + cur, cl, acc)
    if p2:
        return (True, False, [], cl, acc) if e else (False, False, [], [], [cl] + acc)
    return (False, True, [], [], acc) if e else (True, True, [], [], acc)


def readFree(x: Sequence[bool]) -> tuple[int, Fml]:
    """(n, the clauses) from any word (Lean: `FreeCode.readFree`, with `scanR`)."""
    n = ones(x)
    s: RState = (False, False, [], [], [])
    for e in rest(x):
        s = stepR(width(n), s, e)
    return n, [[slotDec(ofWord(cur[::-1])) or (0, False) for cur in cl[::-1]] for cl in s[4][::-1]]


# ---------------------------------------------------------------------------------------------
# the tree


def lv(l: tuple[int, bool]) -> int:
    """The literal (u, b) as the variable 2u if b, 2u + 1 if not (Lean: `EthCor.CnfTree.lv`)."""
    return 2 * l[0] + (0 if l[1] else 1)


def pairF(n: int) -> Fml:
    """x_{2u} ∨ x_{2u+1} and ¬x_{2u} ∨ ¬x_{2u+1} for u < n (Lean: `EthCor.CnfTree.pairF`)."""
    return [C for u in range(n) for C in ([(2 * u, True), (2 * u + 1, True)], [(2 * u, False), (2 * u + 1, False)])]


def rootX(a: tuple[int, Fml]) -> DNode:
    """2n variables, s = n, ψ open, the pair clauses closed (Lean: `EthCor.CnfTree.rootX`)."""
    n, psi = a
    return ((2 * n, n), ([dedup([lv(l) for l in C]) for C in psi], pairF(n)))


def posC(D: list[int]) -> list[tuple[int, bool]]:
    """Variables as a clause of positive literals (Lean: `GraphProblems.posC`)."""
    return [(u, True) for u in D]


def stepD(w: int, x: DNode) -> Optional[tuple[DNode, DNode]]:
    """The light and the heavy child; None if no open clause is longer than w (Lean:
    `GraphProblems.stepD`)."""
    head, (O, F) = x
    C = next((C for C in O if w < len(C)), None)
    if C is None:
        return None
    H = C[:w]
    light = (head, ([D for D in O if D != C], [posC(H)] + F))
    heavy = (head, ([[u for u in D if u not in H] for D in O], [[(u, False)] for u in H] + F))
    return light, heavy


def leafD(x: DNode) -> tuple[int, int, Fml]:
    """(N, s, open clauses as positive clauses ++ closed) (Lean: `GraphProblems.leafD`)."""
    (N, s), (O, F) = x
    return N, s, [posC(D) for D in O] + F


def leaves(step: Callable[[S], Optional[tuple[S, S]]], k: int, s: S) -> list[S]:
    """The leaves below s, light before heavy, cut at depth k (Lean: `Groundwork.Sparsify.leaves`)."""
    if k == 0:
        return [s]
    c = step(s)
    if c is None:
        return [s]
    return leaves(step, k - 1, c[0]) + leaves(step, k - 1, c[1])


def walk_sum(step: Callable[[S], Optional[tuple[S, S]]], root: Callable[[A], S], T: Callable[[S], int], a: A) -> int:
    """The depth-first walk with an explicit stack, T added up at the leaves (Lean:
    `CountKSat.walkSum` = `foldWhile` of `walkNext` and `guard (walkSel step) T 0`)."""
    total = 0
    st: Optional[list[S]] = [root(a)]
    while st is not None:
        if st:  # walkSel: the top, if it is a leaf
            c = step(st[0])
            total += T(st[0]) if c is None else 0
            st = st[1:] if c is None else [c[0], c[1]] + st[1:]  # walkNext
        else:
            st = None  # walkNext [] = none
    return total


def sized(a: tuple[int, int, Fml]) -> int:
    """Anthropic's `FromPrinted.Consequences.SIZED` on (N in unary, s, F): `cntS N s F`."""
    N, s, F = a
    return count_sized(F, N, s)


# ---------------------------------------------------------------------------------------------
# A1: the machine with a fixed width


def cnf_word(x: Sequence[bool], w: int) -> int:
    """The machine `EthCor.CnfTM.cnfM w` on a word: read, walk the tree of `stepD w`, `SIZED` at the
    leaves (Lean writes the sum with `Nat.bits`). The walk does not end for w = 0."""
    if w < 1:
        raise ValueError("the width must be at least 1")
    return walk_sum(lambda y: stepD(w, y), lambda y: rootX(readFree(y)), lambda y: sized(leafD(y)), x)


def count_any_width(F: Fml, n: int, w: int) -> int:
    """`cnfM w` on `SatFree.enc F`: the number of solutions of F on n variables (`cnf_counts`; the
    theorem takes w ≥ 2 from `CnfTree.exists_width`, but every w ≥ 1 gives the count)."""
    return cnf_word(enc(F, n), w)


# ---------------------------------------------------------------------------------------------
# A1′: the width read off the node


def wN(N: int) -> int:
    """2^{⌊L/4⌋ − ⌊lg L⌋} + 1 with L = ⌊lg ⌊lg N⌋⌋, subtraction cut at 0 (Lean:
    `EthCor.GrowTree.wN`). It is 2 for N < 2^16."""
    return 2 ** max(0, log2(log2(N)) // 4 - log2(log2(log2(N)))) + 1


def stepW(x: DNode) -> Optional[tuple[DNode, DNode]]:
    """`stepD` with the width for the N variables of the node (Lean: `EthCor.GrowTree.stepW`)."""
    return stepD(wN(x[0][0]), x)


def leafF(x: DNode) -> Fml:
    """The formula of a leaf without repeated clauses (Lean: `EthCor.GrowTM.leafF`)."""
    return dedup(leafD(x)[2])


def leafM(x: DNode) -> int:
    """The Main Theorem's machine at a leaf, `cntN N (leafF x)` (Lean: `EthCor.GrowTM.leafM`, which
    hands it the compact code `preL x`; the Python counter takes the formula itself)."""
    return count(leafF(x), x[0][0])


def grow_word(x: Sequence[bool]) -> int:
    """The machine `EthCor.GrowTM.growM` on a word: the walk of `stepW`, `leafM` at the leaves."""
    return walk_sum(stepW, lambda y: rootX(readFree(y)), leafM, x)


def count_grow(F: Fml, n: int) -> int:
    """`growM` on `SatFree.enc F`: the number of solutions of F on n variables (`cnf_grow`)."""
    return grow_word(enc(F, n))
