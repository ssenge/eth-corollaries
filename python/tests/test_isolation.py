import random
from itertools import product

import pytest

from ethcor.isolation import H, Seed, card_seed, isolates, random_seed, rows, rv, seeds, wt


def test_rv():
    rng = random.Random(1)
    for _ in range(500):
        M, k = rng.randint(1, 8), rng.randint(1, 5)
        J = tuple(rng.randrange(M) for _ in range(k))
        C = tuple(rng.random() < 0.5 for _ in range(k))
        x = [rng.random() < 0.5 for _ in range(M)]
        # with repetition: an index that occurs twice with coefficient 1 cancels
        want = sum(x[j] * sum(1 for jj, c in zip(J, C) if jj == j and c) for j in range(M)) % 2
        assert rv((J, C), x) == want


def test_one_check():
    """Lean `two_mul_card_rv`: 2·#{ρ : ρ(z) = 0} = 2^k·M^k + 2^k·(M − |z|)^k."""
    for M in range(1, 4):
        for k in range(1, 4):
            rs = list(rows(M, k))
            assert len(rs) == M ** k * 2 ** k
            for z in product((False, True), repeat=M):
                assert 2 * sum(rv(r, z) == 0 for r in rs) == 2 ** k * M ** k + 2 ** k * (M - wt(z)) ** k


def test_card_seed():
    for M, k, t, mm in [(1, 1, 1, 0), (1, 1, 1, 1), (2, 1, 1, 1), (2, 1, 2, 1), (1, 2, 3, 2), (3, 1, 1, 1)]:
        L = list(seeds(M, k, t, mm))
        assert len(L) == len(set(L)) == card_seed(M, k, t, mm)


def test_fixings():
    """With t = 1 every coordinate is fixed, so only the point F itself can pass."""
    rng = random.Random(2)
    for _ in range(200):
        M = rng.randint(1, 6)
        w = random_seed(M, 2, 1, 3, rng)
        x = tuple(b for _, b in w.F)
        for y in product((False, True), repeat=M):
            if y != x:
                assert not H(w, y)


def test_iso_count_exhaustive():
    """Lean `iso_count` on all seeds of tiny types and all nonempty S ⊆ {0,1}^M:
    |Ω|·(2t−1)^M·N^mm ≤ 8(mm+1)·A^mm·V·(2t−1)^{2r}·(2t)^M·#{ω isolating}, if 2|S|·A^mm ≤ (2N)^mm."""
    for M, k, t, mm, r in [(2, 1, 1, 3, 2), (2, 1, 2, 2, 2), (1, 1, 2, 3, 1), (3, 1, 1, 2, 3)]:
        pts = list(product((False, True), repeat=M))
        masks = [sum(1 << i for i, x in enumerate(pts) if H(w, x)) for w in seeds(M, k, t, mm)]
        A = 2 ** k * M ** k + 2 ** k * max(M - r, 0) ** k
        N = M ** k * 2 ** k
        V = sum(1 for z in pts if wt(z) < r)
        Om = card_seed(M, k, t, mm)
        assert Om == len(masks)
        checked = 0
        for S in range(1, 2 ** len(pts)):
            s = bin(S).count("1")
            if 2 * s * A ** mm > (2 * N) ** mm:
                continue
            U = sum(1 for p in masks if bin(p & S).count("1") == 1)
            assert Om * ((2 * t - 1) ** M * N ** mm) <= \
                8 * (mm + 1) * A ** mm * V * (2 * t - 1) ** (2 * r) * (2 * t) ** M * U
            checked += 1
        assert checked > 0


def test_random_seeds_isolate():
    """Statistical, not a proof: with k = 2, t = 2 and mm = 3M + 3 a positive fraction of random seeds
    isolates a point of random sets S."""
    rng = random.Random(3)
    for _ in range(40):
        M = rng.randint(1, 8)
        pts = list(product((False, True), repeat=M))
        S = rng.sample(pts, rng.randint(1, min(len(pts), 24)))
        hits = sum(isolates(random_seed(M, 2, 2, 3 * M + 3, rng), S) for _ in range(300))
        assert hits > 0, (M, S)


def test_seed_checks_input():
    with pytest.raises(ValueError):
        Seed(2, 1, 1, 1, 2, (((0,), (True,)),), (False,), ((0, False), (0, True)))
    with pytest.raises(ValueError):
        random_seed(0, 1, 1, 1, random.Random(0))
