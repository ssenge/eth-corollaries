"""N7, N7′: connected dominating set on graphs of any density, by Cut & Count and the shortening tree.

* N7, parity (theorem `EthCor.CdsTM.cds_parity_tm`): the input is `code G ++ unary ℓ`. The root
  `rootC` of the tree (lean/EthCor/CdsTM.lean, `CdsTree.rootN`) has the 3n variables of
  `Conn.connF`, the target n + ℓ, the n clauses of domination (Anthropic's `GraphProblems.nbhd`)
  open and the clauses `sideF n ++ edgeCC n E` closed. Anthropic's tree `stepD w` shortens the open
  clauses to w literals; at each leaf `SIZED` counts the satisfying assignments with n + ℓ true
  variables; the walk adds up; `postC` keeps bit 1 of the sum. The sum is
  `cntS (3n) (n + ℓ) (connF n E (domF n m))` (`CdsTree.shortensN`), so the bit is the parity of the
  number of connected dominating sets of size ℓ (`Conn.conn_parity`).
* N7′, with one-sided error (`EthCor.CdsITM.cds_randomized`): the input `codeCD G ℓ ω` has a seed ω
  on the vertex bits; the root `rootR` has the variables and the target of `ConnI.ciF`, the clauses
  of domination open and the rest of `ciF n E (domF n m) ω` closed (`formD`).
"""

from __future__ import annotations

from itertools import combinations
from typing import Sequence

from .cnf import Fml
from .cnf_anywidth import DNode, leafD, sized, stepD, walk_sum
from .connected import _connected_in, aR, compF, connF, edgeCC, lC, postC, sdR, seedL, sideF
from .graphs import Matrix, adjB, code, unary
from .hamcycle import EH, dFixes, dRows, dk, dm1, isoF, nH, rest
from .isolation import Seed


def nbhd(n: int, m: Sequence[bool]) -> list[list[int]]:
    """For every v the list v, then its neighbours (Lean: `GraphProblems.nbhd`)."""
    return [[v] + [u for u in range(n) if u != v and adjB(n, m, v, u)] for v in range(n)]


def domF(n: int, m: Sequence[bool]) -> Fml:
    """The clauses of domination (Lean: `GraphProblems.domF = (nbhd n m).map posC`)."""
    return [[(u, True) for u in D] for D in nbhd(n, m)]


def rootN(N: int, s: int, n: int, m: Sequence[bool], F: Fml) -> DNode:
    """N variables, target s, the clauses of domination open, F closed (Lean: `CdsTree.rootN`)."""
    return ((N, s), (nbhd(n, m), list(F)))


def mH(x: Sequence[bool]) -> list[bool]:
    """The matrix: the n·n bits after 1^n 0 (Lean: `CdsTM.mH`)."""
    n = nH(x)
    return list(rest(x)[: n * n])


def rootC(x: Sequence[bool]) -> DNode:
    """The root of `cds_parity_tm` (Lean: `CdsTM.rootC`)."""
    n = nH(x)
    return rootN(n + n + n, n + lC(x), n, mH(x), sideF(n) + edgeCC(n, EH(x)))


def formD(x: Sequence[bool]) -> Fml:
    """The closed clauses of `cds_randomized`: `ciF` for ψ = [] (Lean: `CdsITM.formD`)."""
    n, s = nH(x), sdR(x)
    z = n + n + n
    return (connF(n, EH(x), []) + [[(z, False)]] + isoF(z, z + 1, dk(s), dm1(s), dRows(s), dFixes(s))
            + compF(z + 1, aR(x)))


def rootR(x: Sequence[bool]) -> DNode:
    """The root of `cds_randomized` (Lean: `CdsITM.rootR`)."""
    n, a = nH(x), aR(x)
    return rootN(n + n + n + 1 + a + a, n + lC(x) + a, n, mH(x), formD(x))


def codeCD(adj: Matrix, l: int, w: Seed) -> list[bool]:
    """The input: G, ℓ, the seed (Lean: `CdsITM.codeCD`)."""
    return code(adj) + unary(l) + seedL(w)


def cds_word(x: Sequence[bool], w: int) -> list[bool]:
    """The machine `CdsTM.cdsM w`: walk the tree of `stepD w` from `rootC`, `SIZED` at the leaves,
    `postC` on the sum."""
    if w < 1:
        raise ValueError("the width must be at least 1")
    return postC(walk_sum(lambda y: stepD(w, y), rootC, lambda y: sized(leafD(y)), x))


def cdr_word(x: Sequence[bool], w: int) -> list[bool]:
    """The machine `CdsITM.cdrM w`: the same walk from `rootR`."""
    if w < 1:
        raise ValueError("the width must be at least 1")
    return postC(walk_sum(lambda y: stepD(w, y), rootR, lambda y: sized(leafD(y)), x))


def cds_parity(adj: Matrix, l: int, w: int = 2) -> bool:
    """N7: whether G has an odd number of connected dominating sets of size ℓ, 1 ≤ ℓ ≤ n (Lean:
    `EthCor.CdsTM.cds_parity_tm`; the theorem takes w from `CdsTree.shortensN_exists`, but every
    w ≥ 1 gives the same bit)."""
    return cds_word(code(adj) + unary(l), w)[0]


def cds_randomized(adj: Matrix, l: int, seed: Seed, w: int = 2) -> bool:
    """N7′: the machine's bit out(ω) on `codeCD G ℓ ω` (Lean: `EthCor.CdsITM.cds_randomized`). It is 0
    for every ω if there is no connected dominating set of size ℓ, and the parity of the number of
    those that pass ω otherwise (`ConnI.ci_parity`)."""
    if seed.M != len(adj):
        raise ValueError("the seed must act on the n vertex bits")
    return cdr_word(codeCD(adj, l, seed), w)[0]


def num_cds(adj: Matrix, l: int) -> int:
    """The connected dominating sets of size ℓ (Lean: `CdsTM.numCDS`)."""
    n = len(adj)
    count = 0
    for X in combinations(range(n), l):
        S = set(X)
        if all(v in S or any(adj[v][u] for u in S) for v in range(n)) and _connected_in(adj, list(X)):
            count += 1
    return count
