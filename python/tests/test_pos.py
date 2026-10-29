import random
from itertools import combinations

from ethcor.cds import pos_parity, pos_randomized
from ethcor.connected import _connected_in, num_conn
from ethcor.isolation import random_seed

from test_connected import instances, passes


def positive_cnf(rng, n, D=2):
    """Up to D·n positive clauses of any width, repeats allowed (as `opens` drops them)."""
    return [[(rng.randrange(n), True) for _ in range(rng.randint(1, n))] for _ in range(rng.randint(0, D * n))]


def open_nbhd(adj):
    """Connected total domination: every vertex has a neighbour in X."""
    n = len(adj)
    return [[(u, True) for u in range(n) if adj[v][u]] for v in range(n)]


def test_pos_parity():
    """`pos_parity_tm` against brute force, for random positive CNFs, groups and open neighbourhoods."""
    rng = random.Random(1)
    seen = set()
    for adj in instances(rng, 80, nmax=6):
        n = len(adj)
        psis = [positive_cnf(rng, n), open_nbhd(adj)]
        for psi in psis:
            l = rng.randint(1, n)
            want = num_conn(adj, psi, l) % 2 == 1
            assert pos_parity(adj, l, psi, w=rng.randint(1, 3)) == want, (adj, l, psi)
            seen.add(want)
    assert seen == {False, True}


def test_pos_randomized():
    """out(ω) is the parity of the number of connected solutions of size ℓ that pass ω."""
    rng = random.Random(2)
    seen = set()
    for adj in instances(rng, 40, nmax=5):
        n = len(adj)
        psi = positive_cnf(rng, n)
        l = rng.randint(1, n)
        sols = [set(X) for X in combinations(range(n), l)
                if all(any(v in X for v, _ in C) for C in psi) and _connected_in(adj, list(X))]
        w = random_seed(n, rng.randint(1, 2), rng.randint(1, 3), rng.choice([1, 2, 3]), rng)
        want = sum(passes(w, X) for X in sols) % 2 == 1
        assert pos_randomized(adj, l, w, psi) == want, (adj, l, psi)
        seen.add(want)
    assert seen == {False, True}

