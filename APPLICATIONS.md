# Applications

The greedy theorem turns any fraction $\frac ab$ into whole numbers $n_1 < n_2 < \dots < n_k$ with
$\sum 1/n_i = \frac ab$ and $k \le a$. Anywhere a quantity combines as a sum of reciprocals, this
is a construction with a guarantee: it always succeeds, it uses at most $a$ parts, and no part is
repeated. Every example below can be reproduced with `greedy` from
[scripts/stats.py](scripts/stats.py), and its correctness is the Lean theorem `greedy_sum`.

## 1. Fair division with visible equality

Splitting $a$ identical items among $b$ people, each person gets $\frac ab$. Writing
$\frac ab = \sum \frac1{n_i}$ gives a cutting plan: everyone gets one piece of size $\frac1{n_1}$
of an item, one of size $\frac1{n_2}$, and so on. (Sometimes one item has to be cut into pieces of
two different sizes.)

- 3 loaves, 4 people: $\frac34 = \frac12 + \frac14$. Halve two loaves, quarter one.
- 4 cakes, 13 guests: $\frac4{13} = \frac14 + \frac1{18} + \frac1{468}$.

Every person receives the same multiset of piece sizes, so equality can be checked by eye, and
the distinct sizes mean no one has to count identical pieces. This is the use the Rhind papyrus
was written for. The bound $k \le a$ says nobody gets more pieces than there were items.

The greedy plan is not always the best plan: for 4 cakes and 13 guests, the last piece is tiny.
Theorem 1 guarantees *a* plan, and the paper's growth bound explains why greedy plans have
crumbs.

## 2. Resistors in parallel

Resistors in parallel add by reciprocals: $\frac1R = \sum \frac1{R_i}$. So a resistance of
$\frac ba$ ohms can be built from resistors of whole-number resistances $n_1, \dots, n_k$ ohms
in parallel.

- $3.25\ \Omega = \frac{13}{4}\ \Omega$: put $4\ \Omega$, $18\ \Omega$ and $468\ \Omega$ in parallel.

The theorem guarantees at most $a$ resistors, all of different values, so no value needs to be
stocked twice. The same algebra applies to springs in series and capacitors in series.

## 3. Periodic scheduling

A task that must run once in every $n$ time slots uses a $\frac1n$ share of the machine. To give a
job a share of exactly $\frac ab$, split it into periodic sub-tasks with periods $n_1, \dots, n_k$.
The greedy expansion gives distinct periods and at most $a$ sub-tasks.

Whether a set of periods can actually be interleaved is the *pinwheel scheduling* problem.
Kawamura (STOC 2024) proved that every instance with total density at most $\frac56$ can be
scheduled. So any share $\frac ab \le \frac56$ split greedily gives a feasible schedule. A share
above $\frac56$ needs a direct check.

## 4. A test case for verified algorithms

Termination here does not follow from the input getting smaller: the denominators grow doubly
exponentially. The proof needs an invented measure, the numerator. This is the typical shape of a
termination proof for real code: loops that refine an estimate, Euclid-style algorithms, or
algorithms that reduce a residual.

The formalization shows a small, complete pattern for it in Lean 4:

- the definition is accepted only with a `termination_by` measure, so it cannot loop;
- truncated subtraction on natural numbers is shown to be exact before it is cast to $\mathbb Q$;
- a loop invariant (`le_mul_of_mem_greedy`) carries the ordering through the recursion.

Because the file builds in seconds on top of Mathlib, it also works as a teaching example of
well-founded recursion.

## 5. A base for open problems

The same definitions are a starting point for formal work on open questions about unit fractions:

- **Odd greedy algorithm.** Restrict to odd denominators. Whether this always terminates for
  $\frac ab$ with $b$ odd is open (Guy, *Unsolved Problems in Number Theory*, D11).
- **Erdős–Straus conjecture.** Is $\frac4n$ always a sum of three unit fractions? Candidate
  identities can be checked by Lean's kernel the same way `greedy 4 13 = [4, 18, 468]` is.
