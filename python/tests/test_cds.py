import random
from itertools import combinations

from ethcor.cds import cds_parity, cds_randomized, codeCD, domF, num_cds, rootC, rootR
from ethcor.cnf import count_sized
from ethcor.cnf_anywidth import leafD, leaves, stepD
from ethcor.connected import ciF, connF
from ethcor.graphs import code, edge_list, matrix, random_graph, unary
from ethcor.isolation import random_seed

from test_connected import components, instances, passes


def ref_cds(adj, l):
    """The connected dominating sets of size l, by brute force with union-find."""
    n = len(adj)
    return [set(X) for X in combinations(range(n), l)
            if all(v in X or any(adj[v][u] for u in X) for v in range(n)) and components(adj, X) == 1]


def test_num_cds():
    rng = random.Random(1)
    for adj in instances(rng, 200, nmax=7):
        for l in range(1, len(adj) + 1):
            assert num_cds(adj, l) == len(ref_cds(adj, l))


def test_root_is_connF_of_domF():
    """`leafD` of the root is the formula of Cut & Count for the clauses of domination, on 3n variables
    with target n + ℓ (the identity `hcf` of `cds_parity_tm`)."""
    rng = random.Random(2)
    for adj in instances(rng, 100, nmax=7):
        n = len(adj)
        l = rng.randint(1, n)
        N, s, F = leafD(rootC(code(adj) + unary(l)))
        assert (N, s) == (3 * n, n + l)
        assert F == connF(n, edge_list(adj), domF(n, matrix(adj)))


def test_tree_keeps_the_count():
    """The counts of the leaves add up to the count of the root, for every width (`shortensN`); every
    leaf has width at most w + 4 on 3n variables."""
    rng = random.Random(3)
    for adj in instances(rng, 60, nmax=6):
        n = len(adj)
        l = rng.randint(1, n)
        root = rootC(code(adj) + unary(l))
        N, s, F = leafD(root)
        want = count_sized(F, N, s)
        for w in (1, 2, 3):
            ls = leaves(lambda y: stepD(w, y), 2 * n, root)
            assert all(stepD(w, y) is None for y in ls)
            assert all(len(C) <= w + 4 and all(v < N for v, _ in C) for y in ls for C in leafD(y)[2])
            assert sum(count_sized(leafD(y)[2], N, s) for y in ls) == want


def test_cds_parity():
    rng = random.Random(4)
    seen = set()
    for adj in instances(rng, 120, nmax=7):
        n = len(adj)
        for l in range(1, n + 1):
            want = len(ref_cds(adj, l)) % 2 == 1
            assert cds_parity(adj, l, w=rng.randint(1, 3)) == want, (adj, l)
            seen.add(want)
    assert seen == {False, True}


def test_rootR_is_ciF_of_domF():
    """`leafD` of the root of the randomized machine is `ciF n E (domF n m) ω` with the variables and
    the target of `ci_decide`."""
    rng = random.Random(5)
    for adj in instances(rng, 60, nmax=6):
        n = len(adj)
        l = rng.randint(1, n)
        w = random_seed(n, rng.randint(1, 3), rng.randint(1, 4), rng.choice([1, 2, 3 * n + 3]), rng)
        N, s, F = leafD(rootR(codeCD(adj, l, w)))
        A = w.mm * w.k
        assert (N, s) == (3 * n + 1 + A + A, n + l + A)
        assert F == ciF(n, edge_list(adj), domF(n, matrix(adj)), w)


def test_cds_randomized_parity():
    """out(ω) is the parity of the number of connected dominating sets of size ℓ that pass ω."""
    rng = random.Random(6)
    seen = set()
    for adj in instances(rng, 60, nmax=5):
        n = len(adj)
        l = rng.randint(1, n)
        sols = ref_cds(adj, l)
        w = random_seed(n, rng.randint(1, 2), rng.randint(1, 3), rng.choice([1, 2, 3]), rng)
        want = sum(passes(w, X) for X in sols) % 2 == 1
        assert cds_randomized(adj, l, w) == want, (adj, l, w)
        seen.add(want)
    assert seen == {False, True}


def test_cds_one_sided_error():
    """Seeds as in `cds_randomized` (k = 2, t = 4, mm = 3n + 3): never 1 without a connected dominating
    set of size ℓ, 1 for some seed with one."""
    rng = random.Random(7)
    no = yes = 0
    for adj in instances(rng, 40, nmax=4):
        n = len(adj)
        l = rng.randint(1, n)
        if not ref_cds(adj, l):
            no += 1
            assert not any(cds_randomized(adj, l, random_seed(n, 2, 4, 3 * n + 3, rng)) for _ in range(2))
        elif yes < 6:
            yes += 1
            assert any(cds_randomized(adj, l, random_seed(n, 2, 4, 3 * n + 3, rng)) for _ in range(200)), (adj, l)
    assert no >= 5 and yes == 6
