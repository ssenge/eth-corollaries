"""A5a, A5a′, A5b: Hamiltonian cycles by Cut & Count.

* A5a, parity at bounded degree (theorem `EthCor.HamTM.hc_parity_tm`): the front end reads `code G`,
  writes `hcF n E` (lean/EthCor/HamFormula.lean; one variable per edge, then one side bit per
  vertex), the counter of the Main Theorem counts it, `postH` keeps the low bit (HamTM.lean). Its
  parity is that of the number of Hamiltonian cycles (`EthCor.Ham.hc_parity`).
* A5a′, any degree (`EthCor.HamSTM.hcS_tm`, `hc_parity_sparse`): the same with `hcS n E`, which says
  "two chosen edges at every vertex" with sequential counters, width 3 (HamCounter.lean,
  HamSparseTM.lean).
* A5b, Hamiltonian cycle with one-sided error (`EthCor.HamITM.ham_randomized`): the input is `code G`
  followed by `seedCode ω`; the front end writes `hcI n E ω = hcS n E ++ isoF …`, the checks and
  fixings of ω on the edge bits as Tseitin chains (HamIso.lean, HamIsoTM.lean). The low bit of the
  count is the parity of the number of Hamiltonian cycles that pass ω (`EthCor.HamI.iso_parity`).

Not mirrored: the compact code `encK` that `preH`, `preS`, `preI` write for the counter. Here the
counter takes the formula itself (`formH`, `formS`, `formI`, i.e. the formula before `encK`).
"""

from __future__ import annotations

from typing import Sequence

from .cnf import Fml, count
from .graphs import Matrix, code, edge_list, edges
from .isolation import Row, Seed

Edges = list[tuple[int, int]]

# ---------------------------------------------------------------------------------------------
# Lean list functions and the readers of input words


def ones(x: Sequence[bool]) -> int:
    """The number of leading ones (Lean: `GraphProblems.ones`)."""
    k = 0
    while k < len(x) and x[k]:
        k += 1
    return k


def rest(x: Sequence[bool]) -> list[bool]:
    """The word after the leading ones and the zero that ends them (Lean: `GraphProblems.rest`)."""
    return list(x[ones(x) + 1:])


def dedup(F: Fml) -> Fml:
    """Mathlib's `List.dedup`: drops repeated clauses, keeping the last occurrence of each."""
    seen: set = set()
    out = []
    for C in reversed(F):
        key = tuple(C)
        if key not in seen:
            seen.add(key)
            out.append(C)
    out.reverse()
    return out


def binary(N: int, c: int) -> list[bool]:
    """The bits 0..N of c, low bit first: the machine's output word (Lean: `SatK.binary`)."""
    return [(c >> j) & 1 == 1 for j in range(N + 1)]


def postH(w: Sequence[bool]) -> list[bool]:
    """The last step: the low bit of the count (Lean: `HamTM.postH`)."""
    return [w[0] if w else False]


def nH(x: Sequence[bool]) -> int:
    """n, from `code G` at the start of x (Lean: `HamTM.nH`, via `read1`)."""
    return ones(x)


def EH(x: Sequence[bool]) -> Edges:
    """The edge list of the matrix after 1^n 0 (Lean: `HamTM.EH`)."""
    return edges(nH(x), rest(x))


# ---------------------------------------------------------------------------------------------
# A5a: the formula hcF (HamFormula.lean)


def inc(E: Edges, v: int) -> list[int]:
    """The indices of the edges of E at v (Lean: `Ham.inc`)."""
    return [i for i in range(len(E)) if E[i][0] == v or E[i][1] == v]


def atMost2(I: list[int]) -> Fml:
    """No three distinct ones of the variables in I are all true (Lean: `Ham.atMost2`)."""
    return [[(i, False), (j, False), (k, False)] for i in I for j in I for k in I if i != j and j != k and i != k]


def atLeast2(I: list[int]) -> Fml:
    """Besides any one of the variables in I another one is true, and one is true (Lean: `Ham.atLeast2`)."""
    return [[(j, True) for j in I if j != i] for i in I] + [[(j, True) for j in I]]


def edgeC(m: int, i: int, a: int, b: int) -> Fml:
    """If edge i is chosen, its ends a and b are on the same side (Lean: `Ham.edgeC`)."""
    return [[(i, False), (m + a, False), (m + b, True)], [(i, False), (m + a, True), (m + b, False)]]


def tautC(N: int) -> Fml:
    """x_i ∨ ¬x_i for every variable i < N (Lean: `Ham.tautC`)."""
    return [[(i, True), (i, False)] for i in range(N)]


def hcF(n: int, E: Edges) -> Fml:
    """The Cut & Count formula on m + n variables, m = |E|: x_i (i < m) chooses edge i, s_v = variable
    m + v is the side of v (Lean: `Ham.hcF`)."""
    m = len(E)
    return (tautC(m + n) + [C for v in range(n) for C in atMost2(inc(E, v)) + atLeast2(inc(E, v))]
            + [C for i in range(m) for C in edgeC(m, i, E[i][0], E[i][1])] + [[(m, False)]])


def formH(x: Sequence[bool]) -> Fml:
    """Lean: `HamTM.formH x = (hcF (nH x) (EH x)).dedup`."""
    return dedup(hcF(nH(x), EH(x)))


def hc_parity_word(x: Sequence[bool]) -> list[bool]:
    """The machine of `hc_parity_tm` on the word x: count `formH x` on |E| + n variables, keep the low
    bit. On x = code G (n ≥ 1) the bit is «numHamCycles G is odd»."""
    N = len(EH(x)) + nH(x)
    return postH(binary(N, count(formH(x), N)))


def hc_parity(adj: Matrix) -> bool:
    """A5a: whether G has an odd number of Hamiltonian cycles (Lean: `EthCor.HamTM.hc_parity_tm`)."""
    return hc_parity_word(code(adj))[0]


def num_ham_cycles(adj: Matrix) -> int:
    """The subgraphs H ≤ G with every degree 2 that are connected (Lean: `Ham.numHamCycles`), by
    enumerating the edge sets with all degrees ≤ 2."""
    n = len(adj)
    E = edge_list(adj)
    deg = [0] * n
    chosen: list[tuple[int, int]] = []

    def connected() -> bool:
        if n == 0:
            return False
        nb: list[list[int]] = [[] for _ in range(n)]
        for u, v in chosen:
            nb[u].append(v)
            nb[v].append(u)
        seen, stack = {0}, [0]
        while stack:
            for w in nb[stack.pop()]:
                if w not in seen:
                    seen.add(w)
                    stack.append(w)
        return len(seen) == n

    def rec(i: int) -> int:
        if i == len(E):
            return int(all(d == 2 for d in deg) and connected())
        u, v = E[i]
        r = rec(i + 1)
        if deg[u] < 2 and deg[v] < 2:
            deg[u] += 1
            deg[v] += 1
            chosen.append((u, v))
            r += rec(i + 1)
            chosen.pop()
            deg[u] -= 1
            deg[v] -= 1
        return r

    return rec(0)


# ---------------------------------------------------------------------------------------------
# A5a′: the formula hcS with sequential counters (HamCounter.lean, HamSparseTM.lean)


def stepC(p: int, x: int, c: int) -> Fml:
    """One counter step at the edge variable x, from the counter p to c: c = p ∨ x,
    c + 1 = (p + 1) ∨ (x ∧ p), ¬((p + 1) ∧ x) (Lean: `HamS.stepC`)."""
    return [[(p, False), (c, True)], [(x, False), (c, True)], [(c, False), (p, True), (x, True)],
            [(p + 1, False), (c + 1, True)], [(x, False), (p, False), (c + 1, True)],
            [(c + 1, False), (p + 1, True), (x, True)], [(c + 1, False), (p + 1, True), (p, True)],
            [(p + 1, False), (x, False)]]


def cntC(z: int, L: list[tuple[int, int]]) -> Fml:
    """The counter along L = [(x₁, c₁), …] from the counter z: exactly two of the x are true
    (Lean: `HamS.cntC`)."""
    P = [z] + [c for _, c in L]
    return [C for k in range(len(L)) for C in stepC(P[k], L[k][0], L[k][1])] + [[(P[len(L)] + 1, True)]]


def cb(E: Edges, n: int, v: int, e: int) -> int:
    """The counter of edge e at its end v: m + n + 4e + 2·[v is the second end] (Lean: `HamS.cb`)."""
    return len(E) + n + (4 * e + 2 * min(max(v - E[e][0], 0), 1))


def incC(E: Edges, n: int, v: int) -> list[tuple[int, int]]:
    """The edges at v with their counters (Lean: `HamS.incC`)."""
    return [(e, cb(E, n, v, e)) for e in inc(E, v)]


def zC(E: Edges, n: int) -> int:
    """The start z = 5m + n of every counter; z and z + 1 are false (Lean: `HamS.zC`)."""
    return len(E) + n + 4 * len(E)


def hcS(n: int, E: Edges) -> Fml:
    """Cut & Count with sequential counters, on m + n + (4m + 2) variables (Lean: `HamS.hcS`)."""
    m = len(E)
    z = zC(E, n)
    return (tautC(m + n + (4 * m + 2)) + [C for v in range(n) for C in cntC(z, incC(E, n, v))]
            + [C for i in range(m) for C in edgeC(m, i, E[i][0], E[i][1])]
            + [[(m, False)], [(z, False)], [(z + 1, False)]])


def NS(x: Sequence[bool]) -> int:
    """The number of variables of `hcS` for the input x (Lean: `HamSTM.NS`)."""
    m = len(EH(x))
    return m + nH(x) + (4 * m + 2)


def formS(x: Sequence[bool]) -> Fml:
    """Lean: `HamSTM.formS x = (hcS (nH x) (EH x)).dedup`."""
    return dedup(hcS(nH(x), EH(x)))


def hc_sparse_word(x: Sequence[bool]) -> list[bool]:
    """The machine of `hcS_tm` on the word x: count `formS x` on `NS x` variables, keep the low bit."""
    N = NS(x)
    return postH(binary(N, count(formS(x), N)))


def hc_parity_sparse(adj: Matrix) -> bool:
    """A5a′: whether G has an odd number of Hamiltonian cycles, any degree (Lean:
    `EthCor.HamSTM.hcS_tm`, `hc_parity_sparse`, `hc_parity_bounded`)."""
    return hc_sparse_word(code(adj))[0]


# ---------------------------------------------------------------------------------------------
# A5b: the checks of a seed as Tseitin chains (HamIso.lean)

Rows = list[tuple[list[tuple[int, bool]], bool]]


def xstep(p: int, x: int, a: int, c: bool) -> Fml:
    """a = p ⊕ (c ∧ x) (Lean: `HamI.xstep`)."""
    if c:
        return [[(a, False), (p, True), (x, True)], [(a, False), (p, False), (x, False)],
                [(a, True), (p, False), (x, True)], [(a, True), (p, True), (x, False)]]
    return [[(a, False), (p, True)], [(a, True), (p, False)]]


def _getD(L: Sequence, i: int, d):
    return L[i] if 0 <= i < len(L) else d


def rowF(z: int, B: int, k: int, i: int, L: list[tuple[int, bool]]) -> Fml:
    """The chain of check i on the terms L = [(j_l, c_l)]: variable B + i·k + l is the sum of the first
    l + 1 terms c_l ∧ x_{j_l}; z stands for 0 (Lean: `HamI.rowF`)."""
    out: Fml = []
    for l in range(k):
        j, c = _getD(L, l, (0, False))
        out += xstep(z if l == 0 else B + i * k + (l - 1), j, B + i * k + l, c)
    return out


def isoF(z: int, B: int, k: int, m1: int, rows: Rows, fixes: list[tuple[int, bool]]) -> Fml:
    """The chains of all checks, the right-hand sides of the first m₁, and the fixings as unit clauses
    (Lean: `HamI.isoF`)."""
    return ([C for i in range(len(rows)) for C in rowF(z, B, k, i, rows[i][0])]
            + [[(B + i * k + max(k - 1, 0), rows[i][1])] for i in range(min(m1, len(rows)))]
            + [[q] for q in fixes])


def rowL(rho: Row) -> list[tuple[int, bool]]:
    """A check as its list of terms (j_l, c_l) (Lean: `HamI.rowL`)."""
    return list(zip(rho[0], rho[1]))


def rowsOf(w: Seed) -> Rows:
    """The checks of ω with their right-hand sides (Lean: `HamI.rowsOf`)."""
    return [(rowL(w.R[i]), w.B[i]) for i in range(w.mm)]


def fixesOf(w: Seed) -> list[tuple[int, bool]]:
    """The fixed coordinates of ω with their bits (Lean: `HamI.fixesOf`)."""
    return [(j, b) for j, (v, b) in enumerate(w.F) if v == 0]


def NI(n: int, m: int, mm: int, k: int) -> int:
    """The number of variables of `hcI` (Lean: `HamI.NI`)."""
    return m + n + (4 * m + 2) + mm * k


def hcI(n: int, E: Edges, w: Seed) -> Fml:
    """The formula of the graph with edge list E and the seed ω, the seed acting on the edge bits
    (Lean: `HamI.hcI`)."""
    m = len(E)
    return hcS(n, E) + isoF(zC(E, n), m + n + (4 * m + 2), w.k, w.m, rowsOf(w), fixesOf(w))


# ---------------------------------------------------------------------------------------------
# A5b: the code of a seed and the machine (HamIsoTM.lean)


def ublk(W: int, v: int) -> list[bool]:
    """v in a block of W bits, 1^v 0^{W−v} (Lean: `HamITM.ublk`)."""
    return [True] * v + [False] * max(W - v, 0)


def nm(W: int, b: Sequence[bool], p: int) -> int:
    """The number in block p of a word of W-bit blocks (Lean: `HamITM.nm`)."""
    return ones(b[p * W: p * W + W])


def seedNums(w: Seed) -> list[int]:
    """k, m₁, mm, M, then per check its terms j_l, c_l and its right-hand side, then per coordinate
    0 if it is fixed (else 1) and its bit (Lean: `seedNums`, `rowNums`, `termNums`, `fixNums`)."""
    out = [w.k, w.m, w.mm, w.M]
    for (J, C), b in zip(w.R, w.B):
        for j, c in zip(J, C):
            out += [j, int(c)]
        out.append(int(b))
    for v, b in w.F:
        out += [0 if v == 0 else 1, int(b)]
    return out


def seedCode(w: Seed) -> list[bool]:
    """W = M + k + mm + 1 in unary, then the numbers of ω in blocks of W bits (Lean: `HamITM.seedCode`)."""
    W = w.M + w.k + w.mm + 1
    return [True] * W + [False] + [b for v in seedNums(w) for b in ublk(W, v)]


def dn(s: Sequence[bool], p: int) -> int:
    """The number in block p of the seed part s (Lean: `HamITM.dn`)."""
    return nm(ones(s), rest(s), p)


def dk(s: Sequence[bool]) -> int:
    return dn(s, 0)


def dm1(s: Sequence[bool]) -> int:
    return dn(s, 1)


def dmm(s: Sequence[bool]) -> int:
    return dn(s, 2)


def dM(s: Sequence[bool]) -> int:
    return dn(s, 3)


def dRows(s: Sequence[bool]) -> Rows:
    """The checks read from s (Lean: `HamITM.dRows`)."""
    k = dk(s)
    return [([(dn(s, 4 + (i * (2 * k + 1) + 2 * l)), dn(s, 4 + (i * (2 * k + 1) + (2 * l + 1))) == 1)
              for l in range(k)], dn(s, 4 + (i * (2 * k + 1) + 2 * k)) == 1)
            for i in range(dmm(s))]


def dFixes(s: Sequence[bool]) -> list[tuple[int, bool]]:
    """The fixings read from s (Lean: `HamITM.dFixes`)."""
    k, mm = dk(s), dmm(s)
    return [(j, dn(s, 4 + (mm * (2 * k + 1) + (2 * j + 1))) == 1)
            for j in range(dM(s)) if dn(s, 4 + (mm * (2 * k + 1) + 2 * j)) == 0]


def decode_seedCode(w: Seed) -> bool:
    """The statement of Lean's `decode_seedCode` for ω: the readers give back k, m₁, mm, M, the
    checks and the fixings."""
    s = seedCode(w)
    return (dk(s) == w.k and dm1(s) == w.m and dmm(s) == w.mm and dM(s) == w.M
            and dRows(s) == rowsOf(w) and dFixes(s) == fixesOf(w))


def sI(x: Sequence[bool]) -> list[bool]:
    """What follows the matrix (Lean: `HamITM.sI`)."""
    n = nH(x)
    return rest(x)[n * n:]


def NII(x: Sequence[bool]) -> int:
    """The number of variables (Lean: `HamITM.NII`)."""
    s = sI(x)
    return NS(x) + dmm(s) * dk(s)


def formI(x: Sequence[bool]) -> Fml:
    """`hcS n E ++ isoF …` with the seed read from the word, deduplicated (Lean: `HamITM.formI`)."""
    n, E, s = nH(x), EH(x), sI(x)
    return dedup(hcS(n, E) + isoF(zC(E, n), NS(x), dk(s), dm1(s), dRows(s), dFixes(s)))


def ham_word(x: Sequence[bool]) -> list[bool]:
    """The machine of `hcI_tm` on the word x: count `formI x` on `NII x` variables, keep the low bit."""
    N = NII(x)
    return postH(binary(N, count(formI(x), N)))


def ham_randomized(adj: Matrix, w: Seed) -> bool:
    """A5b: the machine's bit out(ω) on `code G ++ seedCode ω`, ω a seed on the m edge bits (Lean:
    `EthCor.HamITM.ham_randomized`). It is 0 for every ω if G has no Hamiltonian cycle, and it is
    the parity of the number of Hamiltonian cycles that pass ω (`HamI.iso_parity`)."""
    if w.M != len(edge_list(adj)):
        raise ValueError("the seed must act on the m edge bits")
    return ham_word(code(adj) + seedCode(w))[0]
