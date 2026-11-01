# Why the greedy algorithm always works

## Sharing bread like an Egyptian

Ancient Egyptian scribes wrote every fraction as a sum of *different* unit fractions:
$\frac12, \frac13, \frac14, \dots$. Their only exception was $\frac23$, which had its own symbol.
They wrote $\frac34$ as $\frac12 + \frac14$, never as $\frac14 + \frac14 + \frac14$.

This is a practical way to share. Suppose 3 loaves must be split among 4 people.
$\frac34 = \frac12 + \frac14$ says: cut two loaves in half and the third into quarters. Everyone
gets one half and one quarter, and everyone can see the shares are equal. The Rhind papyrus
(about 1550 BCE) opens with a table of such splittings for $\frac{2}{n}$.

Two questions follow. Can **every** fraction be written this way? And if so, how do you find the
pieces?

## The greedy recipe

In 1202 Fibonacci gave a recipe:

> Take the **biggest** unit fraction that fits. Subtract it. Repeat with what is left.

Try $\frac{4}{13}$.

| What is left | Biggest unit fraction that fits | Subtract |
| --- | --- | --- |
| $\frac{4}{13} \approx 0.308$ | $\frac14 = 0.25$ ($\frac13$ is too big) | $\frac4{13} - \frac14 = \frac{3}{52}$ |
| $\frac{3}{52} \approx 0.0577$ | $\frac{1}{18} \approx 0.0556$ ($\frac1{17}$ is too big) | $\frac{3}{52} - \frac{1}{18} = \frac{2}{936} = \frac{1}{468}$ |
| $\frac{1}{468}$ | $\frac{1}{468}$ | $0$, done |

So $\frac{4}{13} = \frac14 + \frac1{18} + \frac1{468}$.

The biggest unit fraction that fits under $\frac ab$ is $\frac1n$ with $n = \lceil b/a \rceil$, the
smallest whole number with $n \ge b/a$.

## Why it can't go on forever

Look at the **numerators** of what was left: $4 \to 3 \to 2 \to 1$ (before cancelling $\frac{2}{936}$).
They went down every time. That is the whole proof.

Here is why the numerator always drops. With $\frac ab$ left, we subtract $\frac1n$:

$$
\frac ab - \frac 1n = \frac{an - b}{bn}.
$$

The new numerator is $an - b$. Because $n$ is the *smallest* number with $an \ge b$, the number
$n - 1$ was too small: $a(n-1) < b$. Rearranged, that says $an - b < a$.

So the numerator is a whole number that keeps shrinking. A whole number can only shrink so many
times before it hits $0$, and when it hits $0$ we are done. Starting from numerator $a$, there
are **at most $a$ steps**.

## Why the pieces are all different

Could the recipe pick $\frac14$ twice? No. After subtracting $\frac1n$, what is left is smaller than
$\frac1n$. So the next piece must be strictly smaller, which means a strictly bigger denominator.
(The paper proves this carefully, since "smaller than $\frac1n$" needs the starting fraction to
be less than $1$.)

In fact the denominators grow very fast. Each one is at least $n(n-1)+1$, where $n$ is the
one before it. After $4$ the next must be at least $4 \cdot 3 + 1 = 13$; in our example it was
$18$, so the one after had to be at least $18 \cdot 17 + 1 = 307$. It was $468$.

## When greedy is not the best

Greedy always works, but it is not always short or tidy.

- $\frac{5}{121}$: greedy gives five pieces, and the last denominator has 25 digits. But
  $\frac{5}{121} = \frac1{33} + \frac1{121} + \frac1{363}$ uses only three small ones.
- $\frac{4}{17}$: greedy needs all 4 steps allowed by the bound, ending with a 7-digit
  denominator.

Finding the *shortest* Egyptian fraction for a given number is much harder, and many questions
about it are still open.

## Checked by a computer

"The numerator keeps shrinking" is easy to say, but the details hide traps. The ceiling has to be
computed exactly, and subtraction of whole numbers must never go below zero. We wrote the whole
argument in the proof assistant **Lean 4**, which checks every step down to the axioms.

| Claim | Where it is checked |
| --- | --- |
| The recipe always stops | Lean accepts the definition `greedy` only after proving the numerator shrinks |
| At most $a$ pieces | `greedy_length_le` |
| The pieces add up to $\frac ab$ | `greedy_sum` |
| The pieces are all different | `greedy_strictly_increasing` |
| Every fraction between 0 and 1 is Egyptian | `exists_egyptian` |

The code is in [Egyptian/Basic.lean](Egyptian/Basic.lean). The full proof is in
[SOLUTION.md](SOLUTION.md), and the paper is [paper/paper.pdf](paper/paper.pdf).

## Try it yourself

1. Run the recipe on $\frac{2}{7}$. (You should get $\frac14 + \frac1{28}$.)
2. Run it on $\frac{3}{7}$. How many steps does it take, and does that match the bound?
3. Show that for any odd $b$, greedy writes $\frac2b$ as exactly two pieces:
   $\frac{2}{b} = \frac{1}{(b+1)/2} + \frac{1}{b(b+1)/2}$.
