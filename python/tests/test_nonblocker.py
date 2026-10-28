import random
from itertools import combinations

from ethcor.graphs import random_graph
from ethcor.nonblocker import has_nonblocker


def brute_nb(adj, k):
    n = len(adj)
    def dom(D):
        return all(v in D or any(adj[v][u] for u in D) for v in range(n))
    return any(dom(set(D)) for s in range(n - k + 1) for D in combinations(range(n), s)) if k <= n else False


def test_nonblocker():
    rng = random.Random(6)
    for _ in range(200):
        n = rng.randint(0, 9)
        G = random_graph(n, rng.random() * 0.6, rng)
        k = rng.randint(0, n)
        assert has_nonblocker(G, k) == brute_nb(G, k), (G, k)
