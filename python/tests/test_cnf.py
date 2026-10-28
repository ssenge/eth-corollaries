import random

from ethcor.cnf import brute_weight_counts, weight_counts


def random_fml(n, m, w, rng):
    return [[(rng.randrange(n + 1), rng.random() < 0.5) for _ in range(rng.randint(0, w))] for _ in range(m)]


def test_counter_matches_brute_force():
    rng = random.Random(1)
    for _ in range(400):
        n = rng.randint(0, 9)
        F = random_fml(n, rng.randint(0, 12), 4, rng)
        assert weight_counts(F, n) == brute_weight_counts(F, n), F
