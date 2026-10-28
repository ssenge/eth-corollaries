import random

from ethcor.cnf import count
from ethcor.graphs import code, edge_list, random_graph
from ethcor.hamcycle import (NI, NII, NS, dedup, decode_seedCode, edgeC, formI, hc_parity, hc_parity_sparse, hcF, hcI,
                             hcS, ham_randomized, isoF, num_ham_cycles, seedCode, stepC, tautC, xstep)
from ethcor.isolation import Seed, random_seed


def ref_cycles(adj):
    """The Hamiltonian cycles as edge sets, by a depth-first search over vertex orders from 0."""
    n = len(adj)
    if n < 3:
        return set()
    out = set()

    def dfs(path, seen):
        if len(path) == n:
            if adj[path[-1]][0]:
                cyc = path + [0]
                out.add(frozenset(frozenset((cyc[i], cyc[i + 1])) for i in range(n)))
            return
        for v in range(1, n):
            if v not in seen and adj[path[-1]][v]:
                seen.add(v)
                path.append(v)
                dfs(path, seen)
                path.pop()
                seen.discard(v)

    dfs([0], {0})
    return out


def complete(n):
    return [[u != v for v in range(n)] for u in range(n)]


def cycle(n):
    return [[(u - v) % n in (1, n - 1) for v in range(n)] for u in range(n)]


def petersen():
    adj = [[False] * 10 for _ in range(10)]
    E = [(i, (i + 1) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)] + [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    for u, v in E:
        adj[u][v] = adj[v][u] = True
    return adj


def graphs(rng, nmax, count_, maxm=16):
    """Complete graphs, cycles, the Petersen graph and random graphs, all with at most maxm edges."""
    out = [complete(n) for n in range(1, 7)] + [cycle(n) for n in range(3, 9)] + [petersen()]
    while len(out) < count_:
        adj = random_graph(rng.randint(1, nmax), rng.choice([0.3, 0.5, 0.7, 0.9]), rng)
        if len(edge_list(adj)) <= maxm:
            out.append(adj)
    return out


def edge_bits(adj, cyc):
    return tuple(frozenset(e) in cyc for e in edge_list(adj))


def passes(w, x):
    """x passes the first m checks and the fixings of the seed, from the fields of the seed."""
    for i in range(w.m):
        J, C = w.R[i]
        if sum(c and x[j] for j, c in zip(J, C)) % 2 != int(w.B[i]):
            return False
    return all(x[j] == b for j, (v, b) in enumerate(w.F) if v == 0)


def test_formulas_as_in_lean():
    """Small cases written out from the Lean definitions of `hcF`, `hcS`, `isoF`, `seedCode`."""
    T, F = True, False
    assert hcF(2, [(0, 1)]) == [[(0, T), (0, F)], [(1, T), (1, F)], [(2, T), (2, F)], [], [(0, T)], [], [(0, T)],
                                [(0, F), (1, F), (2, T)], [(0, F), (1, T), (2, F)], [(1, F)]]
    # m = 1, n = 2: z = 7, the counter of edge 0 at vertex 0 is 3, at vertex 1 it is 5
    assert hcS(2, [(0, 1)]) == (tautC(9) + stepC(7, 0, 3) + [[(4, T)]] + stepC(7, 0, 5) + [[(6, T)]]
                                + edgeC(1, 0, 0, 1) + [[(1, F)], [(7, F)], [(8, F)]])
    rows = [([(0, T), (1, F)], T), ([(1, T), (1, T)], F)]
    assert isoF(10, 20, 2, 1, rows, [(3, T)]) == (xstep(10, 0, 20, T) + xstep(20, 1, 21, F) + xstep(10, 1, 22, T)
                                                   + xstep(22, 1, 23, T) + [[(21, T)]] + [[(3, T)]])
    assert xstep(1, 2, 3, F) == [[(3, F), (1, T)], [(3, T), (1, F)]]
    w = Seed(1, 1, 1, 1, 1, (((0,), (T,)),), (F,), ((0, T),))
    # W = 4; the numbers k, m₁, mm, M, j, c, b, fixed, bit = 1, 1, 1, 1, 0, 1, 0, 0, 1
    blk = {0: [F, F, F, F], 1: [T, F, F, F]}
    assert seedCode(w) == [T, T, T, T, F] + [b for v in [1, 1, 1, 1, 0, 1, 0, 0, 1] for b in blk[v]]


def test_num_ham_cycles():
    rng = random.Random(1)
    for adj in graphs(rng, 8, 150, maxm=28):
        assert num_ham_cycles(adj) == len(ref_cycles(adj)), adj
    assert [num_ham_cycles(complete(n)) for n in range(3, 8)] == [1, 3, 12, 60, 360]


def test_hc_parity():
    rng = random.Random(2)
    for adj in graphs(rng, 8, 200, maxm=22) + [complete(7)]:
        assert hc_parity(adj) == (len(ref_cycles(adj)) % 2 == 1), adj


def test_hcS_has_the_count_of_hcF():
    rng = random.Random(3)
    for adj in graphs(rng, 7, 60, maxm=12):
        n, E = len(adj), edge_list(adj)
        m = len(E)
        assert count(hcS(n, E), m + n + 4 * m + 2) == count(hcF(n, E), m + n), adj


def test_hc_parity_sparse():
    rng = random.Random(4)
    for adj in graphs(rng, 8, 150):
        assert hc_parity_sparse(adj) == (len(ref_cycles(adj)) % 2 == 1), adj


def test_widths():
    rng = random.Random(5)
    for adj in graphs(rng, 8, 40):
        n, E = len(adj), edge_list(adj)
        D = max((sum(r) for r in adj), default=0)
        assert all(len(C) <= D + 3 for C in hcF(n, E))
        assert all(len(C) <= 3 for C in hcS(n, E))
        if E:
            w = random_seed(len(E), 3, 2, 3, rng)
            assert all(len(C) <= 3 for C in hcI(n, E, w))


def test_decode_seedCode():
    rng = random.Random(6)
    for _ in range(300):
        M, k, t, mm = rng.randint(1, 12), rng.randint(1, 4), rng.randint(1, 4), rng.randint(0, 10)
        assert decode_seedCode(random_seed(M, k, t, mm, rng))


def test_front_end_reads_graph_and_seed():
    """Lean `formI_code`: formI (code G ++ seedCode ω) = (hcI n E ω).dedup, NII = NI."""
    rng = random.Random(7)
    for adj in graphs(rng, 7, 40):
        n, E = len(adj), edge_list(adj)
        if not E:
            continue
        w = random_seed(len(E), rng.randint(1, 3), rng.randint(1, 3), rng.randint(1, 6), rng)
        x = code(adj) + seedCode(w)
        assert formI(x) == dedup(hcI(n, E, w))
        assert NII(x) == NI(n, len(E), w.mm, w.k)
        assert NS(code(adj)) == 5 * len(E) + n + 2


def test_iso_parity():
    """out(ω) is the parity of the number of Hamiltonian cycles that pass ω, for every seed."""
    rng = random.Random(8)
    seen = set()
    for _ in range(120):
        n = rng.randint(4, 6)
        adj = random_graph(n, rng.choice([0.6, 0.8, 1.0]), rng)
        m = len(edge_list(adj))
        if m == 0:
            continue
        H = [edge_bits(adj, c) for c in ref_cycles(adj)]
        for _ in range(3):
            w = random_seed(m, rng.randint(1, 3), rng.randint(1, 4), rng.choice([1, 2, 3, 3 * m + 3]), rng)
            want = sum(passes(w, x) for x in H) % 2 == 1
            assert ham_randomized(adj, w) == want, (adj, w)
            seen.add(want)
    assert seen == {False, True}


def test_one_sided_error():
    """Seeds as in `ham_randomized`: k = 2, t = 4, mm = 3m + 3. Never 1 without a Hamiltonian cycle;
    1 for some seed with one."""
    rng = random.Random(9)
    no = yes = 0
    for _ in range(60):
        n = rng.randint(4, 6)
        adj = random_graph(n, rng.choice([0.5, 0.7, 0.9]), rng)
        m = len(edge_list(adj))
        if m == 0:
            continue
        if not ref_cycles(adj):
            no += 1
            assert not any(ham_randomized(adj, random_seed(m, 2, 4, 3 * m + 3, rng)) for _ in range(10))
        elif yes < 8:
            yes += 1
            assert any(ham_randomized(adj, random_seed(m, 2, 4, 3 * m + 3, rng)) for _ in range(400)), adj
    pet = petersen()
    assert not any(ham_randomized(pet, random_seed(15, 2, 4, 48, rng)) for _ in range(3))
    assert no >= 10 and yes == 8
