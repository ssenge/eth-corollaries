import random
from itertools import product

from ethcor.cnf import count_sized
from ethcor.graphs import edge_list
from ethcor.oct import bipartite_in, min_oct, oct_decide, octF

from test_connected import instances


def test_oct_pos():
    """`OctTM.oct_pos`: a solution with n + s true variables exists iff some s vertices induce a
    bipartite subgraph; the count is the number of pairs (Y, proper 2-coloring of G[Y])."""
    rng = random.Random(8)
    for adj in instances(rng, 60, nmax=6):
        n = len(adj)
        F = octF(n, edge_list(adj))
        for s in range(n + 1):
            pairs = sum(1 for Y in product([0, 1], repeat=n) if sum(Y) == s
                        for c in product([0, 1], repeat=n)
                        if all(c[v] == 0 for v in range(n) if not Y[v])
                        and all(c[u] != c[v] for u in range(n) for v in range(u + 1, n) if adj[u][v] and Y[u] and Y[v]))
            assert count_sized(F, 3 * n, n + s) == pairs


def test_oct_decide():
    """`oct_tm` against brute force, for every k."""
    rng = random.Random(9)
    seen = set()
    for adj in instances(rng, 80, nmax=7):
        n = len(adj)
        m = min_oct(adj)
        for k in range(n + 1):
            assert oct_decide(adj, k) == (k >= m), (adj, k)
        seen.add(m)
        assert bipartite_in(adj, range(n)) == (m == 0)
    assert len(seen) >= 3
