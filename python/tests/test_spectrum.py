import random
from itertools import product

from ethcor.spectrum import maxsat_spectrum, specF


def brute_spectrum(F, n):
    spec = [0] * (len(F) + 1)
    for x in product((False, True), repeat=n):
        spec[sum(any(x[v] == b for v, b in C) for C in F)] += 1
    return spec


def random_fml(n, m, r, rng):
    if n == 0:
        return [[] for _ in range(m)]
    return [[(rng.randrange(n), rng.random() < 0.5) for _ in range(rng.randint(0, r))] for _ in range(m)]


def test_maxsat_spectrum():
    rng = random.Random(21)
    for _ in range(200):
        n = rng.randint(0, 7)
        F = random_fml(n, rng.randint(0, 2 * n + 2), 4, rng)
        got = [maxsat_spectrum(F, n, t) for t in range(len(F) + 3)]
        assert got == brute_spectrum(F, n) + [0, 0], (F, n)
        assert sum(got) == 2**n


def test_max_cut():
    """Max-Cut: for an edge (u, v) the clauses x_u ∨ x_v and ¬x_u ∨ ¬x_v; a cut of size c satisfies
    m + c of them."""
    rng = random.Random(22)
    for _ in range(30):
        n = rng.randint(1, 6)
        E = [(u, v) for u in range(n) for v in range(u + 1, n) if rng.random() < 0.5]
        F = [C for u, v in E for C in ([(u, True), (v, True)], [(u, False), (v, False)])]
        cuts = [0] * (len(E) + 1)
        for x in product((False, True), repeat=n):
            cuts[sum(x[u] != x[v] for u, v in E)] += 1
        assert [maxsat_spectrum(F, n, len(E) + c) for c in range(len(E) + 1)] == cuts


def test_specF_shape():
    """`shaped_specF` and `length_specF_le`: width r + 2, variables below 2n + m."""
    rng = random.Random(23)
    for _ in range(100):
        n, r = rng.randint(0, 6), rng.randint(0, 4)
        F = random_fml(n, rng.randint(0, 8), r, rng)
        G = specF(n, F)
        assert all(len(C) <= r + 2 and all(v < 2 * n + len(F) for v, _ in C) for C in G)
        assert len(G) <= 2 * n + len(F) * (r + 1)


def test_edge_cases():
    assert [maxsat_spectrum([], 0, t) for t in range(3)] == [1, 0, 0]
    assert [maxsat_spectrum([[]], 0, t) for t in range(3)] == [1, 0, 0]  # the empty clause is never satisfied
    assert [maxsat_spectrum([], 3, t) for t in range(2)] == [8, 0]
    assert [maxsat_spectrum([[], [(0, True)]], 2, t) for t in range(3)] == [2, 2, 0]
    assert [maxsat_spectrum([[(1, True), (1, False)]], 2, t) for t in range(2)] == [0, 4]  # tautology
    assert [maxsat_spectrum([[(0, True)], [(0, False)]], 1, t) for t in range(3)] == [0, 2, 0]
