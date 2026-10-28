"""CNFs as in the Lean development, and the counters the algorithms call.

A literal is a pair (v, b) with v a variable index and b a Boolean; it holds under an assignment x
iff x[v] == b. A clause is a list of literals, a formula (`Fml` in Lean) a list of clauses. Variables
at or beyond the number n of variables read as False (Lean's `CountKSat.ext`).

The counters:

* `weight_counts(F, n)[s]` is the number of assignments of n variables with exactly s true
  variables that satisfy F. This is Lean's `cntS n s F`, the quantity that Anthropic's machine
  `FromPrinted.Consequences.SIZED` computes.
* `count(F, n)` is the number of satisfying assignments, Lean's `cntN n F`, what the Main Theorem's
  machine computes.

Both use an exact DPLL search with unit-clause preference, component decomposition and caching, which
returns the weight enumerator (a polynomial in z) of the solutions. `brute_weight_counts` enumerates
all 2^n assignments and is used in the tests to cross-check.
"""

from __future__ import annotations

from itertools import product
from typing import Iterable, Sequence

Lit = tuple[int, bool]
Clause = list[Lit]
Fml = list[Clause]


def ext(x: Sequence[bool], v: int) -> bool:
    """Lean's `CountKSat.ext`: the value of variable v, False beyond the assignment."""
    return bool(x[v]) if 0 <= v < len(x) else False


def sat(F: Fml, x: Sequence[bool]) -> bool:
    """x satisfies every clause of F."""
    return all(any(ext(x, v) == b for v, b in C) for C in F)


# ---------------------------------------------------------------------------------------------
# polynomials in z, as coefficient lists


def _padd(p: list[int], q: list[int]) -> list[int]:
    if len(p) < len(q):
        p, q = q, p
    r = list(p)
    for i, c in enumerate(q):
        r[i] += c
    return r


def _pmul(p: list[int], q: list[int]) -> list[int]:
    if not p or not q:
        return []
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return r


def _binom(k: int) -> list[int]:
    """(1 + z)^k."""
    r = [1]
    for _ in range(k):
        r = _padd(r, [0] + r)
    return r


# ---------------------------------------------------------------------------------------------
# the exact counter


def _vars(cl: frozenset) -> set[int]:
    return {abs(l) for C in cl for l in C}


def _assign(cl: frozenset, lit: int):
    """Set the literal lit true; None on a conflict."""
    out = set()
    for C in cl:
        if lit in C:
            continue
        if -lit in C:
            D = C - {-lit}
            if not D:
                return None
            out.add(D)
        else:
            out.add(C)
    return frozenset(out)


def _components(cl: frozenset) -> list[frozenset]:
    parent: dict[int, int] = {}

    def find(a: int) -> int:
        while parent.setdefault(a, a) != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for C in cl:
        vs = [abs(l) for l in C]
        for v in vs[1:]:
            ra, rb = find(vs[0]), find(v)
            if ra != rb:
                parent[ra] = rb
    groups: dict[int, set] = {}
    for C in cl:
        groups.setdefault(find(abs(next(iter(C)))), set()).add(C)
    return [frozenset(g) for g in groups.values()]


def _count(cl: frozenset, memo: dict) -> list[int]:
    """Weight enumerator of the solutions of cl over exactly the variables occurring in cl."""
    if not cl:
        return [1]
    if cl in memo:
        return memo[cl]
    comps = _components(cl)
    if len(comps) > 1:
        r = [1]
        for D in comps:
            r = _pmul(r, _count(D, memo))
        memo[cl] = r
        return r
    vs = _vars(cl)
    unit = next((C for C in cl if len(C) == 1), None)
    if unit is not None:
        v = abs(next(iter(unit)))
    else:
        freq: dict[int, int] = {}
        for C in cl:
            for l in C:
                freq[abs(l)] = freq.get(abs(l), 0) + 1
        v = max(freq, key=freq.get)
    r: list[int] = []
    for lit in (v, -v):
        D = _assign(cl, lit)
        if D is None:
            continue
        p = _pmul(_count(D, memo), _binom(len(vs) - 1 - len(_vars(D))))
        if lit > 0:
            p = [0] + p
        r = _padd(r, p)
    memo[cl] = r
    return r


def _normalize(F: Fml, n: int):
    """Clauses as frozensets of signed integers (v+1 for x_v, -(v+1) for ¬x_v); tautologies and
    clauses made true by a variable beyond n dropped. None if some clause cannot be satisfied."""
    out = set()
    for C in F:
        lits: set[int] = set()
        taut = False
        for v, b in C:
            if v < 0:
                raise ValueError("negative variable index")
            if v >= n:
                if not b:  # x_v reads False, so the literal ¬x_v holds
                    taut = True
                    break
                continue
            l = v + 1 if b else -(v + 1)
            if -l in lits:
                taut = True
                break
            lits.add(l)
        if taut:
            continue
        if not lits:
            return None
        out.add(frozenset(lits))
    return frozenset(out)


def weight_counts(F: Fml, n: int) -> list[int]:
    """c[s] = #{x ∈ {0,1}^n : x ⊨ F, x has exactly s true variables}, s = 0..n (Lean: cntS n s F)."""
    cl = _normalize(F, n)
    if cl is None:
        return [0] * (n + 1)
    p = _pmul(_count(cl, {}), _binom(n - len(_vars(cl))))
    p = p + [0] * (n + 1 - len(p))
    return p[: n + 1]


def count(F: Fml, n: int) -> int:
    """#{x ∈ {0,1}^n : x ⊨ F} (Lean: cntN n F)."""
    return sum(weight_counts(F, n))


def count_sized(F: Fml, n: int, s: int) -> int:
    """The number of solutions with exactly s true variables (Lean: cntS n s F); 0 if s > n."""
    if s < 0 or s > n:
        return 0
    return weight_counts(F, n)[s]


def brute_weight_counts(F: Fml, n: int) -> list[int]:
    """The same as `weight_counts`, by enumerating all 2^n assignments."""
    c = [0] * (n + 1)
    for x in product((False, True), repeat=n):
        if sat(F, x):
            c[sum(x)] += 1
    return c


def assignments(n: int) -> Iterable[tuple[bool, ...]]:
    return product((False, True), repeat=n)
