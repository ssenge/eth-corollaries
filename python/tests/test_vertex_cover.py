import random
from itertools import combinations

from ethcor.graphs import edge_list, random_graph
from ethcor.vertex_cover import degree_for, has_vertex_cover


def brute_vc(adj, k):
    n = len(adj)
    E = edge_list(adj)
    return any(all(u in X or v in X for u, v in E) for s in range(min(k, n) + 1) for X in map(set, combinations(range(n), s)))


def test_vertex_cover():
    rng = random.Random(5)
    for _ in range(150):
        n = rng.randint(0, 9)
        G = random_graph(n, rng.random(), rng)
        k = rng.randint(0, n)
        for d in (1, 2, 3, 5):
            assert has_vertex_cover(G, k, d) == brute_vc(G, k), (G, k, d)


def test_degree_for():
    d = degree_for(1.0)
    import math
    assert (2 / d) * math.log2(math.e * d) <= 0.25
