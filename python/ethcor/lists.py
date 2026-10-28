"""List functions with the semantics of Lean/Mathlib, and the readers of input words."""

from __future__ import annotations

from typing import Hashable, Sequence, TypeVar

T = TypeVar("T")


def _key(a: object) -> Hashable:
    """A hashable stand-in for a, with lists turned into tuples (clauses are lists of literals)."""
    return tuple(_key(b) for b in a) if isinstance(a, list) else a  # type: ignore[return-value]


def dedup(l: Sequence[T]) -> list[T]:
    """Mathlib's `List.dedup`: removes duplicates, keeping the last occurrence of each element."""
    seen: set = set()
    out: list[T] = []
    for a in reversed(l):
        k = _key(a)
        if k not in seen:
            seen.add(k)
            out.append(a)
    out.reverse()
    return out


def idx_of(a: T, l: Sequence[T]) -> int:
    """Lean's `List.idxOf`: the first index of a in l, or len(l) if a is absent."""
    for i, b in enumerate(l):
        if b == a:
            return i
    return len(l)


def ones(x: Sequence[bool]) -> int:
    """The number of leading ones (Lean: `GraphProblems.ones`)."""
    k = 0
    while k < len(x) and x[k]:
        k += 1
    return k


def rest(x: Sequence[bool]) -> list[bool]:
    """The word after the leading ones and the zero that ends them (Lean: `GraphProblems.rest`)."""
    return list(x[ones(x) + 1:])


def log2(n: int) -> int:
    """Lean's `Nat.log2`: ⌊log₂ n⌋, and 0 for n = 0."""
    return n.bit_length() - 1 if n > 0 else 0


def test_bit(c: int, j: int) -> bool:
    return (c >> j) & 1 == 1


def bits(c: int) -> list[bool]:
    """Lean's `Nat.bits`: the binary digits of c, lowest first, no leading zero (empty for 0)."""
    out = []
    while c > 0:
        out.append(c & 1 == 1)
        c >>= 1
    return out
