import random
from itertools import product

from ethcor.colorings import num_colorings, num_hom
from ethcor.graphs import random_graph, random_relation


def brute_colorings(adj, k):
    n = len(adj)
    return sum(all(f[u] != f[v] for u in range(n) for v in range(n) if adj[u][v]) for f in product(range(k), repeat=n))


def brute_hom(adj, H):
    n, h = len(adj), len(H)
    return sum(all(H[f[u]][f[v]] for u in range(n) for v in range(n) if adj[u][v]) for f in product(range(h), repeat=n))


def test_colorings():
    rng = random.Random(2)
    for _ in range(60):
        n = rng.randint(0, 6)
        k = rng.randint(2, 5)
        G = random_graph(n, rng.random(), rng)
        assert num_colorings(G, k) == brute_colorings(G, k)


def test_hom():
    rng = random.Random(3)
    for _ in range(60):
        n = rng.randint(0, 5)
        h = rng.randint(2, 5)
        G = random_graph(n, rng.random(), rng)
        H = random_relation(h, rng.random(), rng)
        assert num_hom(G, H) == brute_hom(G, H)


def test_hom_special_cases():
    rng = random.Random(4)
    for _ in range(20):
        n = rng.randint(1, 6)
        G = random_graph(n, 0.5, rng)
        k = rng.randint(2, 4)
        K = [[a != c for c in range(k)] for a in range(k)]
        assert num_hom(G, K) == brute_colorings(G, k)  # H = K_k: proper colorings
        I = [[True, True], [True, False]]  # an edge with a loop at 0: independent sets (the 1s)
        indep = sum(all(not (S >> u & 1 and S >> v & 1) for u in range(n) for v in range(n) if G[u][v]) for S in range(2 ** n))
        assert num_hom(G, I) == indep
