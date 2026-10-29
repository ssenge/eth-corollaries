import random
from itertools import combinations, product

from ethcor.forest import acyclic_in, fvs_parity, fvs_randomized, num_for, num_fvs
from ethcor.isolation import random_seed

from test_connected import components, instances, passes


def test_sides_edges():
    """`Forest.sides_edges`: S·2^e = 2^{|W|+j}, j = 0 iff acyclic, S the side maps constant on edges."""
    rng = random.Random(4)
    seen = set()
    for adj in instances(rng, 200, nmax=6):
        n = len(adj)
        E = [(u, v) for u, v in combinations(range(n), 2) if adj[u][v]]
        S = sum(1 for s in product([0, 1], repeat=n) if all(s[u] == s[v] for u, v in E))
        P = S * 2 ** len(E)
        j = P.bit_length() - 1 - n
        assert P == 2 ** (n + j) and j >= 0
        acyc = acyclic_in(adj, list(range(n)))
        assert (j == 0) == acyc
        assert j == len(E) - n + components(adj, list(range(n)))  # the cyclomatic number
        seen.add(acyc)
    assert seen == {False, True}


def test_fvs_parity():
    """`fvs_parity_tm` against brute force."""
    rng = random.Random(5)
    seen = set()
    for adj in instances(rng, 80, nmax=6):
        n = len(adj)
        k = rng.randint(0, n)
        want = num_fvs(adj, k) % 2 == 1
        assert num_fvs(adj, k) == num_for(adj, n - k)  # `numFVS_eq`
        assert fvs_parity(adj, k) == want, (adj, k)
        seen.add(want)
    assert seen == {False, True}


def test_fvs_randomized():
    """out(ω) is the parity of the number of induced forests of size n − k that pass ω."""
    rng = random.Random(6)
    seen = set()
    for adj in instances(rng, 40, nmax=5):
        n = len(adj)
        k = rng.randint(0, n)
        forests = [set(X) for X in combinations(range(n), n - k) if acyclic_in(adj, X)]
        w = random_seed(n, rng.randint(1, 2), rng.randint(1, 3), rng.choice([1, 2, 3]), rng)
        want = sum(passes(w, X) for X in forests) % 2 == 1
        assert fvs_randomized(adj, k, w) == want, (adj, k)
        seen.add(want)
    assert seen == {False, True}


def test_fvs_iff():
    """`ForestTM.fvs_iff`: a feedback vertex set with at most k vertices exists iff an induced forest
    with exactly n − k vertices does."""
    rng = random.Random(7)
    for adj in instances(rng, 200, nmax=6):
        n = len(adj)
        for k in range(n + 1):
            le = any(acyclic_in(adj, [v for v in range(n) if v not in X])
                     for j in range(k + 1) for X in combinations(range(n), j))
            assert le == (num_for(adj, n - k) > 0)
