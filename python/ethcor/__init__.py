"""Reference implementations of the algorithms of eth-corollaries.

Every algorithm of the repository is a polynomial-time front end that writes a CNF, one call to a
counter of satisfying assignments, and a small post-step. In the Lean theorems the counter is
Anthropic's 2^{o(n)} machine. Here it is any implementation of the interface in `ethcor.counter`
(by default an exact DPLL counter with component caching), so the front ends can be run and tested on
small instances. The formulas are built exactly as the Lean definitions build them; each module names
the Lean definitions it mirrors.
"""
