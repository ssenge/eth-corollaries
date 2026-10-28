import random
from itertools import permutations

from ethcor.permanent import permanent01, permanent_signed


def brute_perm(M):
    n = len(M)
    total = 0
    for s in permutations(range(n)):
        p = 1
        for i in range(n):
            p *= M[s[i]][i]
        total += p
    return total


def test_permanent01():
    rng = random.Random(7)
    for _ in range(80):
        n = rng.randint(0, 6)
        q = rng.random()
        A = [[rng.random() < q for _ in range(n)] for _ in range(n)]
        assert permanent01(A) == brute_perm([[int(b) for b in r] for r in A])


def test_permanent_signed():
    rng = random.Random(8)
    for _ in range(80):
        n = rng.randint(0, 5)
        q = rng.random()
        A = [[rng.random() < q for _ in range(n)] for _ in range(n)]
        Sg = [[rng.random() < 0.5 for _ in range(n)] for _ in range(n)]
        M = [[(-1 if Sg[i][j] else 1) if A[i][j] else 0 for j in range(n)] for i in range(n)]
        assert permanent_signed(A, Sg) == brute_perm(M)
