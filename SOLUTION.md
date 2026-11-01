# The greedy Egyptian fraction algorithm: termination and term bounds

## Statement

For natural numbers $a, b$ define the **greedy expansion** $G(a, b)$, a finite list of natural numbers, by

$$
G(0, b) = [\,], \qquad
G(a, b) = n :: G(an - b,\; nb) \quad (a > 0), \quad\text{where } n = \left\lceil \tfrac{b}{a} \right\rceil .
$$

In words: subtract the largest unit fraction $1/n$ that does not exceed $a/b$, and repeat on what is left.

**Theorem.** Let $0 < a < b$ and write $G(a,b) = [n_1, \dots, n_k]$. Then

1. **Termination.** The recursion stops, and $k \le a$.
2. **Correctness.** Every $n_i \ge 1$ and
   $$\frac{a}{b} = \frac{1}{n_1} + \frac{1}{n_2} + \cdots + \frac{1}{n_k}.$$
3. **Distinctness.** $n_1 < n_2 < \cdots < n_k$.

**Corollary (Fibonacci, 1202).** Every rational number $q$ with $0 < q < 1$ is a sum of at most $\operatorname{num}(q)$ distinct unit fractions, where $\operatorname{num}(q)$ is the numerator of $q$ in lowest terms.

## Proof

Fix $a > 0$ and let $n = \lceil b/a \rceil$, the least natural number with $na \ge b$. By minimality,

$$
(n-1)\,a < b \le n\,a. \tag{1}
$$

Put $a' = na - b$ and $b' = nb$. These are the arguments of the recursive call.

**Step 1: the numerator drops.** By (1), $a' = na - b < a$. Every recursive call strictly decreases the first argument, a natural number, so the recursion stops after at most $a$ steps. This proves termination and $k \le a$.

**Step 2: each step is exact.** Suppose $b > 0$. Then $n \ge 1$ by (1), and $b' = nb > 0$. Since $na \ge b$, the difference $a' = na - b$ is a genuine (non-truncated) natural number, and

$$
\frac{1}{n} + \frac{a'}{b'} = \frac{b + (na - b)}{nb} = \frac{a}{b}.
$$

By induction on $a$, using $\sum G(0, b') = 0 = 0/b'$ as the base case, the unit fractions of $G(a, b)$ sum to $a/b$.

**Step 3: each term bounds the rest.** We first show that every $m$ in $G(a,b)$ satisfies

$$
b \le m\,a. \tag{2}
$$

The first term $n$ satisfies (2) by (1). For a later term $m$, which lies in $G(a', b')$, induction gives $nb \le m a'$. If $b = 0$, (2) is trivial. Otherwise $n \ge 1$, and $a' < a$, so $b \le nb \le m a' \le m a$.

**Step 4: the denominators increase.** Now assume $0 < a < b$. Let $m$ be any term of $G(a', b')$. Then $a' > 0$, because $G(0, b')$ is empty. By (2) applied to $(a', b')$ we get $m a' \ge b' = nb$. Since $a' < a < b$, we have $nb > na'$. Therefore $m a' > n a'$, and dividing by $a' > 0$ gives $m > n$.

The recursive call still satisfies the hypothesis $a' < b'$, because $a' < a < b \le nb = b'$. So by induction the whole list is strictly increasing.

**Corollary.** Write $q = a/b$ in lowest terms with $0 < a < b$. Then $G(a, b)$ is the required list.

## Example

$$
\frac{4}{13}: \quad n = \lceil 13/4 \rceil = 4,\quad \frac{4}{13} - \frac14 = \frac{3}{52};\quad
n = \lceil 52/3 \rceil = 18,\quad \frac{3}{52} - \frac{1}{18} = \frac{2}{936};\quad
n = \lceil 936/2 \rceil = 468,\quad \text{remainder } 0.
$$

So $\frac{4}{13} = \frac14 + \frac1{18} + \frac1{468}$, with $3 \le 4$ terms. The algorithm runs on the unreduced pair $(a', b')$; reducing at each step can only shorten the list.

## Formalization

All three parts of the theorem and the corollary are proved in Lean 4 with Mathlib, with no `sorry`. See [`Egyptian/Basic.lean`](Egyptian/Basic.lean).

| Statement | Lean name |
| --- | --- |
| Termination | the definition `greedy` is accepted with `termination_by a` |
| $k \le a$ | `greedy_length_le` |
| Terms are positive | `greedy_pos` |
| Sum equals $a/b$ | `greedy_sum` |
| Inequality (2) | `le_mul_of_mem_greedy` |
| Strictly increasing | `greedy_strictly_increasing` |
| Corollary | `exists_egyptian` |
