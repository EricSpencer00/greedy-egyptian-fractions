# Greedy Egyptian fractions in Lean 4

A machine-checked proof that the Fibonacci–Sylvester greedy algorithm writes every rational
$a/b \in (0, 1)$ as a sum of at most $a$ distinct unit fractions.

- [SOLUTION.md](SOLUTION.md): the proof on paper
- [Egyptian/Basic.lean](Egyptian/Basic.lean): the Lean 4 formalization (Mathlib, no `sorry`)
- [paper/paper.pdf](paper/paper.pdf): the paper ([source](paper/paper.tex))
- [EXPOSITION.md](EXPOSITION.md): the idea for a general reader
- [APPLICATIONS.md](APPLICATIONS.md): where the theorem is used
- [scripts/stats.py](scripts/stats.py): reproduces the paper's tables

```bash
lake exe cache get
lake build
python3 scripts/stats.py
```
