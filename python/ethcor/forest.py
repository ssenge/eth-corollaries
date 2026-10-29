"""N9, N9′: induced forests and feedback vertex sets by Cut & Count, for O(n) edges.

* N9, parity (theorem `EthCor.ForestTM.fvs_parity_tm`): the input is `code G ++ unary s`; the front
  end `preF` writes `fvsF n E [] = connF n E [] ++ ebF n E ++ compF 3n m` on 3n + 2m variables
  (an edge bit b_i = 3n + i with b_i → x_u ∧ x_v for the edge i = (u, v), and its complement at
  3n + m + i; lean/EthCor/ForestFormula.lean) with the target n + s + m; Anthropic's `SIZED` counts the
  solutions of that size, and `postF`, which reads s again from the input, keeps bit s of the count.
  A vertex set x contributes sig(x)·2^{e(x)} = 2^{|x| + j}, with j = 0 iff G[x] is a forest
  (`Forest.sides_edges`), so bit s is the parity of the number of induced forests of size s, i.e.
  of the feedback vertex sets of size n − s (`Forest.fvs_parity`, `ForestTM.numFVS_eq`).
* N9′, with one-sided error (`EthCor.ForestITM.fvs_randomized`): the input `codeFI G s ω` has a seed
  ω of `Seed n k t mm` on the vertex bits; the front end `preQ` writes `isoAdd N₀ (fvsF n E []) ω =
  fvsF ++ [z false] ++ isoF … ++ compF …` with N₀ = 3n + 2m, on N₀ + 1 + 2·mm·k variables with target
  n + s + m + mm·k (ForestFormula.lean, ForestIsoTM.lean).
"""

from __future__ import annotations

from typing import Sequence

from .cnf import Fml, assignments
from .connected import _sized, aR, compF, connF, lC, sdR, seedL
from .graphs import Matrix, code, unary
from .hamcycle import EH, Edges, dFixes, dk, dm1, dRows, fixesOf, isoF, nH, rowsOf
from .isolation import Seed


def ebF(n: int, E: Edges) -> Fml:
    """b_i → x_u ∧ x_v for the bit b_i = 3n + i of the edge i = (u, v) (Lean: `Forest.ebF`)."""
    return [C for i, (a, b) in enumerate(E) for C in ([(3 * n + i, False), (a, True)], [(3 * n + i, False), (b, True)])]


def fvsF(n: int, E: Edges, psi: Fml) -> Fml:
    """Lean: `Forest.fvsF n E ψ = connF n E ψ ++ ebF n E ++ compF (3n) m`, on 3n + 2m variables."""
    return connF(n, E, psi) + ebF(n, E) + compF(3 * n, len(E))


def postF(x: Sequence[bool], N: int) -> list[bool]:
    """The last step: bit s of the count, s read from the input (Lean: `ForestTM.postF`)."""
    return [N // 2 ** lC(x) % 2 == 1]


def preF(x: Sequence[bool]) -> tuple[int, int, Fml]:
    """The front end of `for_parity_tm` (Lean: `ForestTM.preF`)."""
    n, E = nH(x), EH(x)
    m = len(E)
    return (n + n + n + m + m, n + lC(x) + m, fvsF(n, E, []))


def for_word(x: Sequence[bool]) -> list[bool]:
    """The machine `forM`: `preF`, `SIZED`, `postF` on the input and the count."""
    return postF(x, _sized(preF(x)))


def fvs_parity(adj: Matrix, k: int) -> bool:
    """N9: whether G has an odd number of feedback vertex sets with k vertices, on the input
    `code G ++ unary (n − k)` (Lean: `EthCor.ForestTM.fvs_parity_tm`)."""
    return for_word(code(adj) + unary(len(adj) - k))[0]


def acyclic_in(adj: Matrix, X: Sequence[int]) -> bool:
    """G[X] has no cycle: no edge inside X closes a cycle of a union-find forest."""
    parent = {v: v for v in X}

    def find(a: int) -> int:
        while parent[a] != a:
            a = parent[a]
        return a

    X = list(X)
    for i, u in enumerate(X):
        for v in X[i + 1:]:
            if adj[u][v]:
                ru, rv = find(u), find(v)
                if ru == rv:
                    return False
                parent[ru] = rv
    return True


def num_for(adj: Matrix, s: int) -> int:
    """The vertex sets of size s that induce a forest (Lean: `ForestTM.numFor`)."""
    n = len(adj)
    return sum(1 for x in assignments(n) if sum(x) == s and acyclic_in(adj, [v for v in range(n) if x[v]]))


def num_fvs(adj: Matrix, k: int) -> int:
    """The feedback vertex sets with k vertices (Lean: `ForestTM.numFVS`)."""
    n = len(adj)
    return sum(1 for x in assignments(n) if sum(x) == k and acyclic_in(adj, [v for v in range(n) if not x[v]]))


# ---------------------------------------------------------------------------------------------
# N9′: the checks of a seed (ForestFormula.lean, `isoAdd`) and the machine (ForestIsoTM.lean)


def isoAdd(N0: int, F: Fml, w: Seed) -> Fml:
    """F, z = N₀ false, the chains of ω at N₀ + 1 + i·k + l, their complements (Lean: `Forest.isoAdd`)."""
    return F + [[(N0, False)]] + isoF(N0, N0 + 1, w.k, w.m, rowsOf(w), fixesOf(w)) + compF(N0 + 1, w.mm * w.k)


def codeFI(adj: Matrix, s: int, w: Seed) -> list[bool]:
    """The input: G, s, the seed (Lean: `ForestITM.codeFI`)."""
    return code(adj) + unary(s) + seedL(w)


def nQ(x: Sequence[bool]) -> int:
    """The number of variables of `fvsF` (Lean: `ForestITM.nQ`)."""
    n, m = nH(x), len(EH(x))
    return n + n + n + m + m


def formQ(x: Sequence[bool]) -> Fml:
    """Lean: `ForestITM.formQ`, i.e. `isoAdd` with G and ω read from the word."""
    n, s, N0 = nH(x), sdR(x), nQ(x)
    return (fvsF(n, EH(x), []) + [[(N0, False)]] + isoF(N0, N0 + 1, dk(s), dm1(s), dRows(s), dFixes(s))
            + compF(N0 + 1, aR(x)))


def preQ(x: Sequence[bool]) -> tuple[int, int, Fml]:
    """The front end of `for_randomized` (Lean: `ForestITM.preQ`)."""
    a = aR(x)
    return (nQ(x) + 1 + a + a, nH(x) + lC(x) + len(EH(x)) + a, formQ(x))


def fi_word(x: Sequence[bool]) -> list[bool]:
    """The machine `fiM`: `preQ`, `SIZED`, `postF` on the input and the count."""
    return postF(x, _sized(preQ(x)))


def fvs_randomized(adj: Matrix, k: int, w: Seed) -> bool:
    """N9′: the machine's bit out(ω) on `codeFI G (n − k) ω`, ω a seed on the n vertex bits (Lean:
    `EthCor.ForestITM.fvs_randomized`). It is 0 for every ω if G has no feedback vertex set with at most
    k vertices, and it is the parity of the number of induced forests of size n − k that pass ω
    (`Forest.fi_parity`)."""
    if w.M != len(adj):
        raise ValueError("the seed must act on the n vertex bits")
    return fi_word(codeFI(adj, len(adj) - k, w))[0]
