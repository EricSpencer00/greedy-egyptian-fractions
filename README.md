# Greedy Egyptian fractions in Lean 4

A machine-checked proof that the Fibonacci–Sylvester greedy algorithm writes every rational
$a/b \in (0, 1)$ as a sum of at most $a$ distinct unit fractions.

- [SOLUTION.md](SOLUTION.md): the proof on paper
- [Egyptian/Basic.lean](Egyptian/Basic.lean): the Lean 4 formalization (Mathlib, no `sorry`)

```bash
lake exe cache get
lake build
```
