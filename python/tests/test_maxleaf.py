import random
from itertools import combinations

from ethcor.cds import maxleaf_randomized, mincds_randomized, num_cds
from ethcor.isolation import random_seed

from test_connected import instances


def spanning_trees(adj):
    """The spanning trees of G, as edge lists, by brute force over the sets of n − 1 edges."""
    n = len(adj)
    E = [(u, v) for u, v in combinations(range(n), 2) if adj[u][v]]
    for T in combinations(E, n - 1):
        parent = list(range(n))

        def find(a):
            while parent[a] != a:
                a = parent[a]
            return a

        ok = True
        for u, v in T:
            a, b = find(u), find(v)
            if a == b:
                ok = False
                break
            parent[a] = b
        if ok:
            yield T


def max_leaves(adj):
    """The largest number of leaves of a spanning tree, or None if G is disconnected."""
    n = len(adj)
    best = None
    for T in spanning_trees(adj):
        deg = [0] * n
        for u, v in T:
            deg[u] += 1
            deg[v] += 1
        leaves = sum(d == 1 for d in deg)
        best = leaves if best is None else max(best, leaves)
    return best


def test_leaf_iff():
    """`Leaf.leaf_iff`: for n ≥ 3 and 1 ≤ L < n, a spanning tree with at least L leaves exists iff a
    connected dominating set of size n − L exists."""
    rng = random.Random(1)
    seen = set()
    for adj in instances(rng, 300, nmax=7):
        n = len(adj)
        if n < 3:
            continue
        ml = max_leaves(adj)
        for L in range(1, n):
            want = ml is not None and ml >= L
            assert (num_cds(adj, n - L) > 0) == want, (adj, L)
            seen.add(want)
    assert seen == {False, True}


def test_cds_le_iff():
    """`Leaf.cds_le_iff`: for ℓ ≤ n, a connected dominating set of size at most ℓ exists iff one of size
    exactly ℓ exists."""
    rng = random.Random(2)
    for adj in instances(rng, 300, nmax=7):
        n = len(adj)
        for l in range(0, n + 1):
            assert any(num_cds(adj, k) for k in range(l + 1)) == (num_cds(adj, l) > 0), (adj, l)


def test_maxleaf_one_sided_error():
    """Seeds as in `cds_randomized` (k = 2, t = 4, mm = 3n + 3): never 1 without a spanning tree with
    L leaves, 1 for some seed with one; the minimum CDS form likewise."""
    rng = random.Random(3)
    no = yes = 0
    for adj in instances(rng, 60, nmax=4):
        n = len(adj)
        if n < 3:
            continue
        L = rng.randint(1, n - 1)
        ml = max_leaves(adj)
        if ml is None or ml < L:
            no += 1
            assert not any(maxleaf_randomized(adj, L, random_seed(n, 2, 4, 3 * n + 3, rng)) for _ in range(2))
        elif yes < 4:
            yes += 1
            assert any(maxleaf_randomized(adj, L, random_seed(n, 2, 4, 3 * n + 3, rng)) for _ in range(200)), (adj, L)
            l = n - ml
            assert any(mincds_randomized(adj, l, random_seed(n, 2, 4, 3 * n + 3, rng)) for _ in range(200)), (adj, l)
    assert no >= 3 and yes == 4
