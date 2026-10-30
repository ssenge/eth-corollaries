import random
from itertools import combinations, product
from math import prod

from test_connected import instances


def comps(adj, X):
    """The vertex sets of the components of G[X]."""
    parent = {v: v for v in X}

    def find(a):
        while parent[a] != a:
            a = parent[a]
        return a

    for u, v in combinations(X, 2):
        if adj[u][v]:
            parent[find(u)] = find(v)
    out = {}
    for v in X:
        out.setdefault(find(v), set()).add(v)
    return list(out.values())


def test_components_product():
    """The step from colorings to power sums used by `EthCor.Barrier`: colorings of X with q colors that
    are constant on the edges of G[X], weighted by ∏_v w[s(v)], sum to ∏_C p_{|C|}(w); with the root's
    color fixed to 0, to w[0]^{|C_r|} ∏_{C ≠ C_r} p_{|C|}(w)."""
    rng = random.Random(10)
    for adj in instances(rng, 60, nmax=6):
        n = len(adj)
        X = [v for v in range(n) if rng.random() < 0.7] or [0]
        q = rng.randint(1, 3)
        w = [rng.randint(-2, 3) for _ in range(q)]
        p = lambda k: sum(x ** k for x in w)
        good = [s for s in product(range(q), repeat=len(X))
                if all(s[i] == s[j] for i, j in combinations(range(len(X)), 2) if adj[X[i]][X[j]])]
        Cs = comps(adj, X)
        assert sum(prod(w[a] for a in s) for s in good) == prod(p(len(C)) for C in Cs)
        Cr = next(C for C in Cs if X[0] in C)
        rooted = sum(prod(w[a] for a in s) for s in good if s[0] == 0)
        assert rooted == w[0] ** len(Cr) * prod(p(len(C)) for C in Cs if C is not Cr)
