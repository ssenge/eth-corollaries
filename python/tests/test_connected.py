import random
from itertools import combinations

from ethcor.cnf import weight_counts
from ethcor.connected import (ciF, codeCI, conn_parity, conn_randomized, connF, cvc_parity, cvc_randomized, enc_free,
                              num_conn, num_cvc, preC, preR, read_free, steiner, vcF)
from ethcor.graphs import code, edge_list, random_graph, unary
from ethcor.isolation import Seed, random_seed


def components(adj, X):
    """The number of connected components of G[X], by union-find."""
    parent = {v: v for v in X}

    def find(a):
        while parent[a] != a:
            a = parent[a]
        return a

    for u, v in combinations(X, 2):
        if adj[u][v]:
            parent[find(u)] = find(v)
    return len({find(v) for v in X})


def holds(psi, X):
    return all(any((v in X) == b for v, b in C) for C in psi)


def ref_sets(adj, l, ok):
    """The vertex sets X with |X| = l, ok(X) and G[X] connected."""
    return [set(X) for X in combinations(range(len(adj)), l) if ok(set(X)) and components(adj, X) == 1]


def is_cover(adj, X):
    n = len(adj)
    return all(u in X or v in X for u in range(n) for v in range(u + 1, n) if adj[u][v])


def random_psi(n, rng):
    return [[(rng.randrange(n), rng.random() < 0.6) for _ in range(rng.randint(1, 3))] for _ in range(rng.randint(0, 3))]


def instances(rng, count_, nmax=7):
    for _ in range(count_):
        n = rng.randint(1, nmax)
        yield random_graph(n, rng.choice([0.2, 0.4, 0.6, 0.8]), rng)


def passes(w, X):
    x = [v in X for v in range(w.M)]
    for i in range(w.m):
        J, C = w.R[i]
        if sum(c and x[j] for j, c in zip(J, C)) % 2 != int(w.B[i]):
            return False
    return all(x[j] == b for j, (v, b) in enumerate(w.F) if v == 0)


def test_formulas_as_in_lean():
    """Small cases written out from the Lean definitions of `connF`, `sideF`, `edgeCC`, `ciF`."""
    T, F = True, False
    assert connF(2, [(0, 1)], [[(0, T)]]) == [
        [(0, T)],
        [(2, T), (4, T)], [(2, F), (4, F)], [(0, T), (2, F)], [(3, T), (5, T)], [(3, F), (5, F)], [(1, T), (3, F)],
        [(0, F), (1, F), (2, F), (3, T)], [(0, F), (1, F), (2, T), (3, F)]]
    w = Seed(1, 1, 1, 1, 1, (((0,), (T,)),), (T,), ((0, F),))
    assert ciF(1, [], [], w) == [
        [(1, T), (2, T)], [(1, F), (2, F)], [(0, T), (1, F)],
        [(3, F)],
        [(4, F), (3, T), (0, T)], [(4, F), (3, F), (0, F)], [(4, T), (3, F), (0, T)], [(4, T), (3, T), (0, F)],
        [(4, T)], [(0, F)],
        [(4, T), (5, T)], [(4, F), (5, F)]]
    assert enc_free(2, [[(1, T)], []]) == [T, T, F, T, T, F, F, T, F, T, F, F]


def test_read_free():
    """Lean `readFree_enc_append`: the reader gives back n and φ, whatever follows the code."""
    rng = random.Random(1)
    for _ in range(300):
        n = rng.randint(0, 9)
        phi = [] if n == 0 else [[(rng.randrange(n), rng.random() < 0.5) for _ in range(rng.randint(0, 4))]
                                 for _ in range(rng.randint(0, 5))]
        junk = [rng.random() < 0.5 for _ in range(rng.randint(0, 10))]
        assert read_free(enc_free(n, phi) + junk) == (n, phi)


def test_connF_counts_side_maps():
    """cntS (3n) (n + ℓ) (connF n E ψ) = Σ 2^{cc(G[X])} over the X with |X| = ℓ and X ⊨ ψ."""
    rng = random.Random(2)
    for adj in instances(rng, 150):
        n = len(adj)
        psi = random_psi(n, rng)
        c = weight_counts(connF(n, edge_list(adj), psi), 3 * n)
        for l in range(n + 1):
            want = sum(2 ** components(adj, X) for X in combinations(range(n), l) if holds(psi, set(X)))
            assert c[n + l] == want


def test_conn_parity():
    rng = random.Random(3)
    for adj in instances(rng, 200, nmax=8):
        n = len(adj)
        for l in range(1, n + 1):
            psi = random_psi(n, rng)
            want = len(ref_sets(adj, l, lambda X: holds(psi, X)))
            assert conn_parity(adj, l, psi) == (want % 2 == 1), (adj, l, psi)
            assert num_conn(adj, psi, l) == want


def test_steiner_parity():
    rng = random.Random(4)
    for adj in instances(rng, 150):
        n = len(adj)
        T = rng.sample(range(n), rng.randint(1, min(3, n)))
        for l in range(1, n + 1):
            want = len(ref_sets(adj, l, lambda X: set(T) <= X))
            assert conn_parity(adj, l, steiner(T)) == (want % 2 == 1), (adj, l, T)


def test_cvc_parity():
    rng = random.Random(5)
    for adj in instances(rng, 200, nmax=8):
        n = len(adj)
        for l in range(1, n + 1):
            want = len(ref_sets(adj, l, lambda X: is_cover(adj, X)))
            assert cvc_parity(adj, l) == (want % 2 == 1), (adj, l)
            assert num_cvc(adj, l) == want


def test_front_ends_read_the_input():
    """Lean `read_conn` and `read_ci`."""
    rng = random.Random(6)
    for adj in instances(rng, 60):
        n, E = len(adj), edge_list(adj)
        l = rng.randint(1, n)
        psi = random_psi(n, rng)
        assert preC(code(adj) + unary(l) + enc_free(n, psi)) == (3 * n, n + l, connF(n, E, psi))
        w = random_seed(n, rng.randint(1, 3), rng.randint(1, 3), rng.randint(1, 3 * n + 3), rng)
        A = w.mm * w.k
        assert preR(codeCI(adj, l, w, psi)) == (3 * n + 1 + A + A, n + l + A, ciF(n, E, psi, w))


def test_ci_parity():
    """out(ω) is the parity of the number of connected solutions of size ℓ that pass ω, for every seed."""
    rng = random.Random(7)
    seen = set()
    for adj in instances(rng, 150, nmax=6):
        n = len(adj)
        l = rng.randint(1, n)
        psi = random_psi(n, rng) if rng.random() < 0.5 else vcF(edge_list(adj))
        sols = ref_sets(adj, l, lambda X: holds(psi, X))
        for _ in range(2):
            w = random_seed(n, rng.randint(1, 3), rng.randint(1, 4), rng.choice([1, 2, 3, 3 * n + 3]), rng)
            want = sum(passes(w, X) for X in sols) % 2 == 1
            assert conn_randomized(adj, l, w, psi) == want, (adj, l, psi, w)
            seen.add(want)
    assert seen == {False, True}


def test_one_sided_error():
    """Seeds as in `conn_randomized`: k = 2, t = 4, mm = 3n + 3. Never 1 without a connected solution of
    size ℓ; 1 for some seed with one. Connected vertex cover and Steiner tree."""
    rng = random.Random(8)
    no = yes = 0
    for adj in instances(rng, 80, nmax=6):
        n = len(adj)
        l = rng.randint(1, n)
        T = rng.sample(range(n), rng.randint(1, min(3, n)))
        for ok, run in [(lambda X: is_cover(adj, X), lambda w: cvc_randomized(adj, l, w)),
                        (lambda X: set(T) <= X, lambda w: conn_randomized(adj, l, w, steiner(T)))]:
            if not ref_sets(adj, l, ok):
                no += 1
                assert not any(run(random_seed(n, 2, 4, 3 * n + 3, rng)) for _ in range(5))
            elif yes < 16:
                yes += 1
                assert any(run(random_seed(n, 2, 4, 3 * n + 3, rng)) for _ in range(400)), (adj, l, T)
    assert no >= 20 and yes == 16
