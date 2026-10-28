"""The isolation lemma for arbitrary sets, with sparse parity checks.

Lean: namespace `EthCor.Iso` (lean/EthCor/Isolation.lean, IsoBound.lean), after Calabro, Impagliazzo,
Kabanets and Paturi. A seed ω of `Seed M k t mm` is the number m ≤ mm of checks to use, mm parity
checks on k coordinates each (indices with repetition, coefficients) with their right-hand sides,
and for every coordinate a value in range(t) and a bit; the coordinate is fixed to the bit when the
value is 0. `H(ω, x)`: x passes the first m checks and the fixings. ω isolates a point of S when
exactly one x ∈ S passes (`(S.filter (H ω)).card = 1`). Theorem `EthCor.Iso.isolation`: for every
δ > 0 there are k and t such that for all large M and every nonempty S ⊆ {0,1}^M at least a fraction
2^{−δM} of the seeds of `Seed M k t (3M + 3)` isolate a point of S.
"""

from __future__ import annotations

import random
from dataclasses import dataclass
from itertools import product
from typing import Iterable, Iterator, Sequence

Row = tuple[tuple[int, ...], tuple[bool, ...]]
"""A parity check (Lean: `Row M k = (Fin k → Fin M) × (Fin k → Bool)`): indices and coefficients."""


def wt(z: Sequence[bool]) -> int:
    """The Hamming weight (Lean: `wt`)."""
    return sum(1 for b in z if b)


def hd(x: Sequence[bool], y: Sequence[bool]) -> int:
    """The Hamming distance (Lean: `hd`)."""
    return sum(1 for a, b in zip(x, y) if a != b)


def rv(rho: Row, x: Sequence[bool]) -> int:
    """The value Σ_l c_l·x_{j_l} mod 2 of a check on x (Lean: `rv`, in ZMod 2)."""
    J, C = rho
    return sum(1 for j, c in zip(J, C) if c and x[j]) % 2


def bz(b: bool) -> int:
    """A bit as an element of ZMod 2 (Lean: `bz`)."""
    return 1 if b else 0


def rowsOK(m: int, R: Sequence[Row], B: Sequence[bool], x: Sequence[bool]) -> bool:
    """x passes the first m checks of (R, B) (Lean: `rowsOK`)."""
    return all(rv(R[i], x) == bz(B[i]) for i in range(min(m, len(R))))


def fixOK(F: Sequence[tuple[int, bool]], x: Sequence[bool]) -> bool:
    """x agrees with the fixed coordinates of F (Lean: `fixOK`)."""
    return all(x[j] == b for j, (v, b) in enumerate(F) if v == 0)


@dataclass(frozen=True)
class Seed:
    """An element of Lean's `Seed M k t mm = Fin (mm + 1) × ((Fin mm → Row M k) × (Fin mm → Bool)) ×
    (Fin M → Fin t × Bool)`: `m` = ω.1, `R` = ω.2.1.1, `B` = ω.2.1.2, `F` = ω.2.2."""

    M: int
    k: int
    t: int
    mm: int
    m: int
    R: tuple[Row, ...]
    B: tuple[bool, ...]
    F: tuple[tuple[int, bool], ...]

    def __post_init__(self) -> None:
        M, k, t, mm = self.M, self.k, self.t, self.mm
        ok = (0 <= self.m <= mm and len(self.R) == mm and len(self.B) == mm and len(self.F) == M
              and all(len(J) == k and len(C) == k and all(0 <= j < M for j in J) for J, C in self.R)
              and all(0 <= v < t for v, _ in self.F))
        if not ok:
            raise ValueError("not a seed of Seed M k t mm")


def H(w: Seed, x: Sequence[bool]) -> bool:
    """x passes the checks and the fixings of ω (Lean: `H ω x = rowsOK ω.1 ω.2.1.1 ω.2.1.2 x ∧ fixOK ω.2.2 x`)."""
    return rowsOK(w.m, w.R, w.B, x) and fixOK(w.F, x)


def passing(w: Seed, S: Iterable[Sequence[bool]]) -> list[Sequence[bool]]:
    """The points of S that pass ω (Lean: `S.filter (H ω)`)."""
    return [x for x in S if H(w, x)]


def isolates(w: Seed, S: Iterable[Sequence[bool]]) -> bool:
    """Exactly one point of S passes ω (Lean: `(S.filter (H ω)).card = 1`)."""
    return len(passing(w, S)) == 1


def card_seed(M: int, k: int, t: int, mm: int) -> int:
    """|Seed M k t mm| = (mm+1)·((M^k·2^k)^mm·2^mm)·(2t)^M (Lean: `card_seed`)."""
    return (mm + 1) * ((M ** k * 2 ** k) ** mm * 2 ** mm) * (2 * t) ** M


def random_seed(M: int, k: int, t: int, mm: int, rng: random.Random) -> Seed:
    """A uniformly random element of `Seed M k t mm`."""
    if card_seed(M, k, t, mm) == 0:
        raise ValueError("Seed M k t mm is empty")
    bit = lambda: rng.getrandbits(1) == 1  # noqa: E731
    R = tuple((tuple(rng.randrange(M) for _ in range(k)), tuple(bit() for _ in range(k))) for _ in range(mm))
    return Seed(M, k, t, mm, rng.randrange(mm + 1), R, tuple(bit() for _ in range(mm)),
                tuple((rng.randrange(t), bit()) for _ in range(M)))


def rows(M: int, k: int) -> Iterator[Row]:
    """All of `Row M k`."""
    for J in product(range(M), repeat=k):
        for C in product((False, True), repeat=k):
            yield (J, C)


def seeds(M: int, k: int, t: int, mm: int) -> Iterator[Seed]:
    """All of `Seed M k t mm` (only for tiny parameters: there are `card_seed` of them)."""
    rs = list(rows(M, k))
    fs = list(product(range(t), (False, True)))
    for m in range(mm + 1):
        for R in product(rs, repeat=mm):
            for B in product((False, True), repeat=mm):
                for F in product(fs, repeat=M):
                    yield Seed(M, k, t, mm, m, R, B, F)
