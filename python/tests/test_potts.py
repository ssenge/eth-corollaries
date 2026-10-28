import random
from fractions import Fraction
from itertools import combinations, product

import pytest

from ethcor.graphs import edge_list, random_graph
from ethcor.potts import pottsF, potts_spectrum, tutte_hyperbola


def brute_spectrum(adj, q):
    E = edge_list(adj)
    N = [0] * (len(E) + 1)
    for s in product(range(q), repeat=len(adj)):
        N[sum(s[u] == s[v] for u, v in E)] += 1
    return N


def components(n, A):
    seen, k = set(), 0
    for r in range(n):
        if r in seen:
            continue
        k += 1
        todo = [r]
        seen.add(r)
        while todo:
            a = todo.pop()
            for u, v in A:
                for b in (v if u == a else None, u if v == a else None):
                    if b is not None and b not in seen:
                        seen.add(b)
                        todo.append(b)
    return k


def brute_tutte(adj, x, y):
    """The rank-generating function Σ_{A ⊆ E} (x−1)^{k(A)−k(E)}·(y−1)^{|A|+k(A)−n}."""
    n, E = len(adj), edge_list(adj)
    kE = components(n, E)
    return sum((x - 1) ** (components(n, A) - kE) * (y - 1) ** (len(A) + components(n, A) - n)
               for s in range(len(E) + 1) for A in combinations(E, s))


def test_potts_spectrum():
    rng = random.Random(31)
    for _ in range(120):
        n = rng.randint(0, 6)
        q = rng.randint(1, 4)
        G = random_graph(n, rng.random(), rng)
        m = len(edge_list(G))
        assert [potts_spectrum(G, q, j) for j in range(m + 3)] == brute_spectrum(G, q) + [0, 0], (G, q)


def test_pottsF_shape():
    """`shaped_pottsF` and `length_pottsF_le`: width q + 3, variables below nq + m."""
    rng = random.Random(32)
    for _ in range(50):
        n, q = rng.randint(0, 6), rng.randint(0, 4)
        E = edge_list(random_graph(n, rng.random(), rng))
        F = pottsF(n, q, E)
        assert all(len(C) <= q + 3 and all(v < n * q + len(E) for v, _ in C) for C in F)
        assert len(F) <= n * (q * q + 1) + len(E) * (q * 2)


def test_tutte_hyperbola():
    rng = random.Random(33)
    for _ in range(40):
        n = rng.randint(0, 5)
        G = random_graph(n, rng.random(), rng)
        q = rng.randint(1, 3)
        for y in (Fraction(0), Fraction(2), Fraction(-1), Fraction(1, 2), Fraction(5, 3)):
            x = 1 + Fraction(q) / (y - 1)
            assert tutte_hyperbola(G, q, y) == brute_tutte(G, x, y), (G, q, y)


def test_chromatic():
    """At (1 − q, 0): P(G, q) = (−1)^{n−k(E)}·q^{k(E)}·T(G; 1 − q, 0), and P(G, q) = N_0."""
    rng = random.Random(34)
    for _ in range(30):
        n = rng.randint(1, 6)
        G = random_graph(n, rng.random(), rng)
        q = rng.randint(1, 4)
        k = components(n, edge_list(G))
        proper = sum(all(s[u] != s[v] for u, v in edge_list(G)) for s in product(range(q), repeat=n))
        assert (-1) ** (n - k) * q**k * tutte_hyperbola(G, q, 0) == proper == potts_spectrum(G, q, 0)


def test_edge_cases():
    assert [potts_spectrum([], 3, j) for j in range(2)] == [1, 0]  # n = 0: one coloring
    assert [potts_spectrum([], 0, j) for j in range(2)] == [1, 0]
    K3 = [[u != v for v in range(3)] for u in range(3)]
    assert [potts_spectrum(K3, 0, j) for j in range(4)] == [0, 0, 0, 0]  # no colors, no colorings
    assert [potts_spectrum(K3, 1, j) for j in range(5)] == [0, 0, 0, 1, 0]  # one color: all mono
    assert [potts_spectrum(K3, 3, j) for j in range(4)] == [6, 18, 0, 3]
    E2 = [[False] * 2 for _ in range(2)]  # no edges: j = 0 counts all colorings
    assert [potts_spectrum(E2, 3, j) for j in range(2)] == [9, 0]
    assert tutte_hyperbola([], 2, 3) == 1
    with pytest.raises(ValueError):
        tutte_hyperbola(K3, 2, 1)
