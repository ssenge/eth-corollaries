"""The Python front ends write exactly the formulas of the Lean front ends.

For random small inputs, the input word goes to both: to `lean/Dump.lean`, which runs the Lean
definitions (`EthCor.formOf`, `Hom.formHom`, `Spectrum.preS`, `PottsTM.preP`, `PermTM.leafP`,
`SPermTM.leafS`, `HamTM.formH`, `HamSTM.formS`, `HamITM.formI`, `ConnTM.preC`, `preV`,
`ConnITM.preR`, `NbTM.preN`, the leaves of `Vc.stepV` with `leafV`, of `stepD` with `leafD` and of
`GrowTree.stepW` with `GrowTM.leafF`), and to the Python functions of the same names. The outputs
must be equal clause for clause.

Needs the built Lean development (`cd lean && lake build`); skipped if `lake` is not on the PATH or
ETHCOR_SKIP_LEAN is set. One run of Lean loads Mathlib, so all queries go in one batch.
"""

from __future__ import annotations

import json
import os
import random
import shutil
import subprocess
from pathlib import Path

import pytest

from ethcor import cnf_anywidth as ca
from ethcor import colorings, connected, hamcycle, nonblocker, permanent, potts, spectrum, vertex_cover
from ethcor.graphs import code, matrix, random_graph, random_relation, unary
from ethcor.isolation import random_seed

LEAN = Path(__file__).resolve().parents[2] / "lean"

pytestmark = pytest.mark.skipif(shutil.which("lake") is None or "ETHCOR_SKIP_LEAN" in os.environ,
                                reason="needs lake and the built Lean development")


def bits(x: list[bool]) -> str:
    return "".join("1" if b else "0" for b in x)


def norm(v):
    """Python values in the JSON shape of Dump.lean: bools as 0/1, tuples as lists."""
    if isinstance(v, bool):
        return int(v)
    if isinstance(v, (list, tuple)):
        return [norm(u) for u in v]
    return v


def random_cnf(n: int, m: int, r: int, rng: random.Random):
    return [[(rng.randrange(n), rng.random() < 0.5) for _ in range(rng.randint(1, r))] for _ in range(m)] if n else []


def cases(rng: random.Random):
    """(name, arg, word, expected) for every front end."""
    out = []
    for _ in range(6):
        n = rng.randint(0, 5)
        G = random_graph(n, 0.5, rng)
        k = rng.randint(2, 4)
        x = unary(k) + code(G)
        out.append(("col", 0, x, colorings.formOf(x)))
        h = rng.randint(2, 3)
        H = random_relation(h, 0.6, rng)
        x = unary(h) + matrix(H) + code(G)
        out.append(("hom", 0, x, colorings.formHom(x)))
        q = rng.randint(1, 3)
        x = code(G) + unary(rng.randint(0, 3))
        out.append(("potts", q, x, potts.preP(q, x)))
        out.append(("hcF", 0, code(G), hamcycle.formH(code(G))))
        out.append(("hcS", 0, code(G), hamcycle.formS(code(G))))
        x = code(G) + unary(rng.randint(1, max(n, 1)))
        out.append(("cvc", 0, x, connected.preV(x)))
        x = code(G) + unary(rng.randint(0, n))
        out.append(("nb", 0, x, nonblocker.preN(x)))
        d = rng.randint(1, 3)
        x = code(G) + unary(rng.randint(0, n))
        out.append(("vc", d, x, [vertex_cover.leafV(d, y) for y in vertex_cover.leaves(d, vertex_cover.rootV(x))]))
        A = random_relation(n, 0.6, rng)
        S = random_relation(n, 0.4, rng)
        x = unary(n) + matrix(A)
        out.append(("perm", 0, x, permanent.leafP(x)))
        x = [rng.random() < 0.5] + unary(n) + matrix(A) + matrix(S)
        out.append(("sperm", 0, x, permanent.leafS(x)))
        nv = rng.randint(1, 4)
        F = random_cnf(nv, rng.randint(0, 4), 4, rng)
        x = unary(rng.randint(0, len(F) + 1)) + ca.enc(F, nv)
        out.append(("spec", 0, x, spectrum.preS(x)))
        w = rng.randint(1, 3)
        x = ca.enc(F, nv)
        out.append(("cnf", w, x, [ca.leafD(y) for y in ca.leaves(lambda y: ca.stepD(w, y), 1000, ca.rootX(ca.readFree(x)))]))
        out.append(("grow", 0, x, [[y[0][0], ca.leafF(y)] for y in ca.leaves(ca.stepW, 1000, ca.rootX(ca.readFree(x)))]))
        if n >= 1:
            phi = random_cnf(n, rng.randint(0, 3), 3, rng)
            l = rng.randint(1, n)
            x = code(G) + unary(l) + connected.enc_free(n, phi)
            out.append(("conn", 0, x, connected.preC(x)))
            kk, t = rng.randint(1, 2), rng.randint(1, 2)
            w_v = random_seed(n, kk, t, 3 * n + 3, rng)
            x = connected.codeCI(G, l, w_v, phi)
            out.append(("ci", 0, x, connected.preR(x)))
            m = len(hamcycle.EH(code(G)))
            if m >= 1:
                w_e = random_seed(m, kk, t, 3 * m + 3, rng)
                x = code(G) + hamcycle.seedCode(w_e)
                out.append(("hcI", 0, x, hamcycle.formI(x)))
    return out


def test_python_matches_lean():
    rng = random.Random(20261028)
    cs = cases(rng)
    query = "".join(f"{name} {arg} {bits(x)}\n" for name, arg, x, _ in cs)
    res = subprocess.run(["lake", "env", "lean", "--run", "Dump.lean"], cwd=LEAN, input=query,
                         capture_output=True, text=True, timeout=3600, check=True)
    lines = res.stdout.strip().splitlines()
    assert len(lines) == len(cs)
    seen = set()
    for (name, arg, x, expected), line in zip(cs, lines):
        assert json.loads(line) == norm(expected), f"{name} arg={arg} on {bits(x)}"
        seen.add(name)
    assert seen == {"col", "hom", "potts", "hcF", "hcS", "hcI", "cvc", "conn", "ci", "nb", "vc", "perm",
                    "sperm", "spec", "cnf", "grow"}
