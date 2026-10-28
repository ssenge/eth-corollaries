import random
from itertools import product

import pytest

from ethcor.cnf_anywidth import (
    count_any_width,
    count_grow,
    enc,
    leafD,
    leaves,
    pairF,
    readFree,
    rootX,
    sized,
    stepD,
    walk_sum,
    wN,
)


def brute_count(F, n):
    return sum(all(any(x[v] == b for v, b in C) for C in F) for x in product((False, True), repeat=n))


def random_fml(n, m, w, rng):
    if n == 0:
        return [[] for _ in range(m)]
    return [[(rng.randrange(n), rng.random() < 0.5) for _ in range(rng.randint(0, w))] for _ in range(m)]


def test_count_any_width():
    rng = random.Random(11)
    for _ in range(300):
        n = rng.randint(0, 7)
        F = random_fml(n, rng.randint(0, 3 * n + 2), n + 3, rng)
        w = rng.randint(1, 4)
        assert count_any_width(F, n, w) == brute_count(F, n), (F, n, w)


def test_count_grow():
    rng = random.Random(12)
    for _ in range(200):
        n = rng.randint(0, 7)
        F = random_fml(n, rng.randint(0, 3 * n + 2), n + 3, rng)
        assert count_grow(F, n) == brute_count(F, n), (F, n)


def test_tree_as_in_shortens_of():
    """The claims of `CnfTree.shortens_of` that do not involve ε, on random instances."""
    rng = random.Random(13)
    for _ in range(100):
        n = rng.randint(1, 6)
        F = random_fml(n, rng.randint(0, 2 * n), n + 3, rng)
        D = max(1, -(-len(F) // n))
        w = rng.randint(2, 4)
        L = leaves(lambda x: stepD(w, x), (D + 2) * n, rootX((n, F)))
        for x in L:
            N, s, G = leafD(x)
            assert stepD(w, x) is None and (N, s) == (2 * n, n)
            assert all(len(C) <= w and all(v < 2 * n for v, _ in C) for C in G)
            assert len(G) <= (2 * D + 4) * n
        assert sum(sized(leafD(x)) for x in L) == brute_count(F, n)
        assert walk_sum(lambda x: stepD(w, x), rootX, lambda x: sized(leafD(x)), (n, F)) == brute_count(F, n)


def test_read_enc():
    rng = random.Random(14)
    for _ in range(200):
        n = rng.randint(0, 9)
        F = random_fml(n, rng.randint(0, 6), 5, rng)
        assert readFree(enc(F, n)) == (n, F)
    T, O = True, False
    # n = 2: 3 bits per literal; x_1 is slot 4 = 001 (low bit first)
    assert enc([[(1, True)]], 2) == [T, T, O] + [T, T, O, O, T, O] + [O]
    with pytest.raises(ValueError):
        enc([[(2, True)]], 2)


def test_root_and_step():
    # the clause x_0 ∨ ¬x_1 ∨ x_0: lv gives [0, 3, 0], dedup keeps the last copy
    root = rootX((2, [[(0, True), (1, False), (0, True)]]))
    assert root == ((4, 2), ([[3, 0]], pairF(2)))
    light, heavy = stepD(1, root)
    assert light == ((4, 2), ([], [[(3, True)]] + pairF(2)))
    assert heavy == ((4, 2), ([[0]], [[(3, False)]] + pairF(2)))
    assert stepD(2, root) is None


def test_edge_cases():
    assert count_any_width([], 0, 2) == 1
    assert count_any_width([[]], 0, 2) == 0
    assert count_any_width([], 3, 2) == 8
    assert count_any_width([[(0, True)], []], 3, 2) == 0
    assert count_any_width([[(0, True), (0, False)]], 3, 1) == 8  # tautology
    assert count_any_width([[(1, True), (1, True)]], 3, 1) == 4  # repeated literal
    assert count_any_width([[(v, b) for v in range(4) for b in (True, False)]], 4, 2) == 16
    assert count_any_width([[(v, True) for v in range(5)]], 5, 1) == 31
    for F, n in [([], 0), ([[]], 0), ([], 3), ([[(2, False)]], 3)]:
        assert count_grow(F, n) == brute_count(F, n)
    with pytest.raises(ValueError):
        count_any_width([[(0, True)]], 1, 0)


def test_wN():
    assert all(wN(N) == 2 for N in range(0, 70000, 7))
    assert wN(2 ** (2**16)) == 2  # L = 16, ⌊lg L⌋ = 4
    assert wN(2 ** (2**20)) == 3  # L = 20: 2^{5 − 4} + 1
    assert wN(2 ** (2**24)) == 5  # L = 24: 2^{6 − 4} + 1
