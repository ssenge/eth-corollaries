"""N2, N2′: connected solutions (Steiner tree, connected vertex cover) by Cut & Count.

* N2, parity of the connected solutions (theorems `EthCor.ConnTM.conn_parity_tm`, `cvc_parity_tm`):
  the input is `code G ++ unary ℓ ++ SatFree.enc φ` (resp. `code G ++ unary ℓ`); the front end `preC`
  (resp. `preV`) writes `connF n E ψ` on 3n variables (vertex bit x_v = v, side bit s_v = n + v, its
  complement n + n + v; lean/EthCor/ConnFormula.lean) with the target n + ℓ for the number of true
  variables; Anthropic's `SIZED` counts the solutions of that size, `postC` keeps bit 1 of the count
  (ConnTM.lean). That bit is the parity of the number of X ⊆ V with |X| = ℓ, X ⊨ ψ and G[X] connected
  (`EthCor.Conn.conn_parity`). With ψ the terminals (unit clauses) these are the Steiner trees on ℓ
  vertices, with ψ = `vcF E` the connected vertex covers.
* N2′, with one-sided error (`EthCor.ConnITM.conn_randomized`): the input `codeCI G ℓ ω φ` has a seed
  ω of `Seed n k t mm` on the vertex bits in it; the front end `preR` writes `ciF n E ψ ω = connF ++
  [z false] ++ isoF … ++ compF …` on 3n + 1 + 2·mm·k variables with target n + ℓ + mm·k (ConnIso.lean,
  ConnIsoTM.lean). Bit 1 of the sized count is the parity of the number of connected solutions of
  size ℓ that pass ω (`EthCor.ConnI.ci_parity`).
"""

from __future__ import annotations

from typing import Sequence

from .cnf import Fml, assignments, count_sized, sat
from .graphs import Matrix, code, edge_list, unary
from .hamcycle import EH, Edges, dk, dm1, dmm, dFixes, dRows, isoF, fixesOf, nH, ones, rest, rowsOf, sI, seedCode
from .isolation import Seed

# ---------------------------------------------------------------------------------------------
# The code of a CNF on the n vertices: Anthropic's `SatFree.enc` and `FreeCode.readFree`


def enc_free(n: int, phi: Fml) -> list[bool]:
    """Lean's `SatFree.enc φ` for φ : Sat3.CNF n: 1ⁿ 0, then per clause 1, (1, literal)*, 0, then 0. A
    literal (v, b) is its slot 2v + 1 + b in ⌊log₂ 2n⌋ + 1 bits, low bit first (`encLit`, `Sat3.slot`)."""
    w = (2 * n).bit_length() if n > 0 else 1
    out = [True] * n + [False]
    for C in phi:
        out.append(True)
        for v, b in C:
            if not 0 <= v < n:
                raise ValueError("a literal of a CNF on n variables")
            s = 2 * v + 1 + int(b)
            out += [True] + [(s >> j) & 1 == 1 for j in range(w)]
        out.append(False)
    return out + [False]


def _stepR(w: int, s: tuple, e: bool) -> tuple:
    p1, p2, cur, cl, acc = s
    if p1:
        if p2:
            return s
        if len(cur) + 1 == w:
            return (False, True, (), ((e,) + cur,) + cl, acc)
        return (True, False, (e,) + cur, cl, acc)
    if p2:
        if e:
            return (True, False, (), cl, acc)
        return (False, False, (), (), (cl,) + acc)
    if e:
        return (False, True, (), (), acc)
    return (True, True, (), (), acc)


def read_free(x: Sequence[bool]) -> tuple[int, Fml]:
    """Lean's `FreeCode.readFree`: n = the leading ones, then one pass of the reader `stepR` over the
    rest; every word of bits is read as a literal by `slotDec` (default (0, false))."""
    n = ones(x)
    w = (2 * n).bit_length() if n > 0 else 1  # Decode.width
    s: tuple = (False, False, (), (), ())
    for e in rest(x):
        s = _stepR(w, s, e)

    def lit(cur: tuple) -> tuple[int, bool]:
        v = sum(int(b) << i for i, b in enumerate(reversed(cur)))  # ofWord cur.reverse
        return (0, False) if v == 0 else ((v - 1) // 2, (v - 1) % 2 == 1)

    return n, [[lit(cur) for cur in reversed(cl)] for cl in reversed(s[4])]


# ---------------------------------------------------------------------------------------------
# N2: the formula connF (ConnFormula.lean) and the machines (ConnTM.lean)


def sideF(n: int) -> Fml:
    """s̄_v = ¬s_v, and s_v = 0 if v is not in the set (Lean: `Conn.sideF`)."""
    return [C for v in range(n) for C in
            ([(n + v, True), (n + n + v, True)], [(n + v, False), (n + n + v, False)], [(v, True), (n + v, False)])]


def edgeCC(n: int, E: Edges) -> Fml:
    """s_u = s_v on the edges inside the set (Lean: `Conn.edgeCC`)."""
    return [C for a, b in E for C in
            ([(a, False), (b, False), (n + a, False), (n + b, True)], [(a, False), (b, False), (n + a, True), (n + b, False)])]


def connF(n: int, E: Edges, psi: Fml) -> Fml:
    """Lean: `Conn.connF n E ψ = ψ ++ sideF n ++ edgeCC n E`, on 3n variables."""
    return list(psi) + sideF(n) + edgeCC(n, E)


def vcF(E: Edges) -> Fml:
    """Every edge has an end in the set (Lean: `ConnTM.vcF`)."""
    return [[(a, True), (b, True)] for a, b in E]


def postC(N: int) -> list[bool]:
    """The last step: bit 1 of the count (Lean: `ConnTM.postC`)."""
    return [N // 2 % 2 == 1]


def lC(x: Sequence[bool]) -> int:
    """ℓ, in unary after the matrix (Lean: `ConnTM.lC`)."""
    return ones(sI(x))


def fC(x: Sequence[bool]) -> Fml:
    """φ, after ℓ (Lean: `ConnTM.fC`)."""
    return read_free(rest(sI(x)))[1]


def preC(x: Sequence[bool]) -> tuple[int, int, Fml]:
    """The front end of `conn_parity_tm`: (number of variables, target size, formula) (Lean: `ConnTM.preC`)."""
    n = nH(x)
    return (n + n + n, n + lC(x), connF(n, EH(x), fC(x)))


def preV(x: Sequence[bool]) -> tuple[int, int, Fml]:
    """The front end of `cvc_parity_tm` (Lean: `ConnTM.preV`)."""
    n, E = nH(x), EH(x)
    return (n + n + n, n + lC(x), connF(n, E, vcF(E)))


def _sized(p: tuple[int, int, Fml]) -> int:
    """What `FromPrinted.Consequences.SIZED` computes on (1^N, s, F): cntS N s F."""
    N, s, F = p
    return count_sized(F, N, s)


def conn_word(x: Sequence[bool]) -> list[bool]:
    """The machine `connM` of `conn_parity_tm`: `preC`, `SIZED`, `postC`."""
    return postC(_sized(preC(x)))


def cvc_word(x: Sequence[bool]) -> list[bool]:
    """The machine `cvcM` of `cvc_parity_tm`: `preV`, `SIZED`, `postC`."""
    return postC(_sized(preV(x)))


def conn_parity(adj: Matrix, l: int, psi: Fml) -> bool:
    """N2: whether the number of X with |X| = ℓ, X ⊨ ψ, G[X] connected is odd, for 1 ≤ ℓ ≤ n and ψ a CNF
    on the vertex bits (Lean: `EthCor.ConnTM.conn_parity_tm`)."""
    return conn_word(code(adj) + unary(l) + enc_free(len(adj), psi))[0]


def cvc_parity(adj: Matrix, l: int) -> bool:
    """N2: whether G has an odd number of connected vertex covers of size ℓ (Lean:
    `EthCor.ConnTM.cvc_parity_tm`)."""
    return cvc_word(code(adj) + unary(l))[0]


def steiner(terminals: Sequence[int]) -> Fml:
    """ψ for Steiner tree: every terminal is in the set."""
    return [[(v, True)] for v in terminals]


def _connected_in(adj: Matrix, X: list[int]) -> bool:
    if not X:
        return False
    S = set(X)
    seen, stack = {X[0]}, [X[0]]
    while stack:
        u = stack.pop()
        for v in S:
            if adj[u][v] and v not in seen:
                seen.add(v)
                stack.append(v)
    return len(seen) == len(S)


def num_conn(adj: Matrix, psi: Fml, l: int) -> int:
    """#{x ∈ {0,1}^n : x ⊨ ψ, |x| = ℓ, G[x] connected} (Lean: `Conn.numConnF`)."""
    n = len(adj)
    return sum(1 for x in assignments(n)
               if sum(x) == l and sat(psi, x) and _connected_in(adj, [v for v in range(n) if x[v]]))


def num_cvc(adj: Matrix, l: int) -> int:
    """The connected vertex covers of size ℓ (Lean: `ConnTM.numCVC`)."""
    return num_conn(adj, vcF(edge_list(adj)), l)


# ---------------------------------------------------------------------------------------------
# N2′: the checks of a seed on the vertex bits (ConnIso.lean) and the machine (ConnIsoTM.lean)


def compF(B: int, A: int) -> Fml:
    """The bits B + A + i are the complements of the bits B + i, i < A (Lean: `ConnI.compF`)."""
    return [C for i in range(A) for C in ([(B + i, True), (B + A + i, True)], [(B + i, False), (B + A + i, False)])]


def ciF(n: int, E: Edges, psi: Fml, w: Seed) -> Fml:
    """`connF`, z = 3n false, the chains of ω at 3n + 1 + i·k + l, their complements; on
    3n + 1 + 2·mm·k variables (Lean: `ConnI.ciF`)."""
    z = n + n + n
    return (connF(n, E, psi) + [[(z, False)]] + isoF(z, z + 1, w.k, w.m, rowsOf(w), fixesOf(w))
            + compF(z + 1, w.mm * w.k))


def seedL(w: Seed) -> list[bool]:
    """The code of a seed with its length in unary in front (Lean: `ConnITM.seedL`)."""
    s = seedCode(w)
    return unary(len(s)) + s


def codeCI(adj: Matrix, l: int, w: Seed, phi: Fml) -> list[bool]:
    """The input: G, ℓ, the seed, φ (Lean: `ConnITM.codeCI`)."""
    return code(adj) + unary(l) + seedL(w) + enc_free(len(adj), phi)


def r2(x: Sequence[bool]) -> list[bool]:
    """What follows ℓ and the length of the seed (Lean: `ConnITM.r2`)."""
    return rest(rest(sI(x)))


def sdR(x: Sequence[bool]) -> list[bool]:
    """The seed part (Lean: `ConnITM.sdR`)."""
    return r2(x)[:ones(rest(sI(x)))]


def fR(x: Sequence[bool]) -> Fml:
    """The formula φ (Lean: `ConnITM.fR`)."""
    return read_free(r2(x)[ones(rest(sI(x))):])[1]


def aR(x: Sequence[bool]) -> int:
    """The number of chain bits (Lean: `ConnITM.aR`)."""
    s = sdR(x)
    return dmm(s) * dk(s)


def formR(x: Sequence[bool]) -> Fml:
    """Lean: `ConnITM.formR`, i.e. `ciF` with G, φ and ω read from the word."""
    n, s = nH(x), sdR(x)
    z = n + n + n
    return (connF(n, EH(x), fR(x)) + [[(z, False)]] + isoF(z, z + 1, dk(s), dm1(s), dRows(s), dFixes(s))
            + compF(z + 1, aR(x)))


def preR(x: Sequence[bool]) -> tuple[int, int, Fml]:
    """The front end of `conn_randomized` (Lean: `ConnITM.preR`)."""
    n, a = nH(x), aR(x)
    return (n + n + n + 1 + a + a, n + lC(x) + a, formR(x))


def ci_word(x: Sequence[bool]) -> list[bool]:
    """The machine `ciM` of `conn_randomized`: `preR`, `SIZED`, `postC`."""
    return postC(_sized(preR(x)))


def conn_randomized(adj: Matrix, l: int, w: Seed, psi: Fml) -> bool:
    """N2′: the machine's bit out(ω) on `codeCI G ℓ ω φ`, ω a seed on the n vertex bits (Lean:
    `EthCor.ConnITM.conn_randomized`). It is 0 for every ω if there is no connected solution of size
    ℓ, and it is the parity of the number of those that pass ω (`ConnI.ci_parity`)."""
    if w.M != len(adj):
        raise ValueError("the seed must act on the n vertex bits")
    return ci_word(codeCI(adj, l, w, psi))[0]


def cvc_randomized(adj: Matrix, l: int, w: Seed) -> bool:
    """N2′ for connected vertex cover: `conn_randomized` with φ = the edges."""
    return conn_randomized(adj, l, w, vcF(edge_list(adj)))
