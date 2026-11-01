import Mathlib

/-!
# The greedy Egyptian fraction algorithm

`greedy a b` lists the denominators that the Fibonacci–Sylvester greedy algorithm produces
for `a / b`. We prove it stops after at most `a` terms, that its unit fractions sum to `a / b`,
and that for `0 < a < b` the denominators are strictly increasing.
-/

namespace Egyptian

/-- One greedy step on `(a + 1) / b` uses `n = ⌈b / (a + 1)⌉ = (b + a) / (a + 1)`. -/
def greedy : ℕ → ℕ → List ℕ
  | 0, _ => []
  | a + 1, b =>
    let n := (b + a) / (a + 1)
    n :: greedy ((a + 1) * n - b) (n * b)
termination_by a => a
decreasing_by
  have := Nat.div_mul_le_self (b + a) (a + 1)
  rw [Nat.mul_comm]
  omega

/-- The ceiling bounds `(n - 1) * (a + 1) < b ≤ n * (a + 1)`, stated without subtraction. -/
lemma ceil_bounds (a b : ℕ) :
    b ≤ (b + a) / (a + 1) * (a + 1) ∧ (b + a) / (a + 1) * (a + 1) ≤ b + a := by
  have h1 := Nat.div_add_mod (b + a) (a + 1)
  have h2 := Nat.mod_lt (b + a) (show 0 < a + 1 by omega)
  constructor
  · rw [Nat.mul_comm]; omega
  · exact Nat.div_mul_le_self _ _

@[simp] lemma greedy_zero (b : ℕ) : greedy 0 b = [] := by
  rw [greedy]

lemma greedy_succ (a b : ℕ) :
    greedy (a + 1) b =
      (b + a) / (a + 1) :: greedy ((a + 1) * ((b + a) / (a + 1)) - b) ((b + a) / (a + 1) * b) := by
  rw [greedy]

/-- The algorithm uses at most `a` unit fractions. -/
theorem greedy_length_le : ∀ a b : ℕ, (greedy a b).length ≤ a
  | 0, b => by simp
  | a + 1, b => by
    rw [greedy_succ, List.length_cons]
    have ih := greedy_length_le ((a + 1) * ((b + a) / (a + 1)) - b) ((b + a) / (a + 1) * b)
    have := (ceil_bounds a b).2
    have := Nat.mul_comm (a + 1) ((b + a) / (a + 1))
    omega
termination_by a => a
decreasing_by
  have := (ceil_bounds a b).2
  rw [Nat.mul_comm]
  omega

/-- Every denominator is positive when `b` is. -/
theorem greedy_pos : ∀ a b : ℕ, 0 < b → ∀ m ∈ greedy a b, 0 < m
  | 0, b, _ => by simp
  | a + 1, b, hb => by
    rw [greedy_succ]
    have hn : 0 < (b + a) / (a + 1) := Nat.div_pos (by omega) (Nat.succ_pos a)
    intro m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact hn
    · exact greedy_pos _ _ (Nat.mul_pos hn hb) m hm
termination_by a => a
decreasing_by
  have := (ceil_bounds a b).2
  rw [Nat.mul_comm]
  omega

/-- The unit fractions sum to `a / b`. -/
theorem greedy_sum : ∀ a b : ℕ, 0 < b →
    ((greedy a b).map (fun m : ℕ => (1 : ℚ) / m)).sum = a / b
  | 0, b, _ => by simp
  | a + 1, b, hb => by
    rw [greedy_succ, List.map_cons, List.sum_cons]
    set n := (b + a) / (a + 1) with hn_def
    have hn : 0 < n := Nat.div_pos (by omega) (Nat.succ_pos a)
    have hle : b ≤ (a + 1) * n := by
      have := (ceil_bounds a b).1; rw [Nat.mul_comm]; exact this
    rw [greedy_sum _ _ (Nat.mul_pos hn hb), Nat.cast_sub hle]
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    push_cast
    field_simp
    ring
termination_by a => a
decreasing_by
  have := (ceil_bounds a b).2
  rw [Nat.mul_comm]
  omega

/-- Every denominator `m` satisfies `b ≤ m * a`, i.e. `1 / m ≤ a / b`. -/
theorem le_mul_of_mem_greedy : ∀ a b : ℕ, ∀ m ∈ greedy a b, b ≤ m * a
  | 0, b => by simp
  | a + 1, b => by
    rw [greedy_succ]
    set n := (b + a) / (a + 1) with hn_def
    have hb := (ceil_bounds a b).1
    have hup := (ceil_bounds a b).2
    rw [← hn_def] at hb hup
    intro m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact hb
    · have ih := le_mul_of_mem_greedy _ _ m hm
      -- ih : n * b ≤ m * ((a + 1) * n - b), and (a + 1) * n - b ≤ a
      have ha' : (a + 1) * n - b ≤ a := by rw [Nat.mul_comm]; omega
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0] at hb; omega
      · calc b ≤ n * b := Nat.le_mul_of_pos_left b hpos
          _ ≤ m * ((a + 1) * n - b) := ih
          _ ≤ m * (a + 1) := Nat.mul_le_mul_left m (by omega)
termination_by a => a
decreasing_by
  rw [Nat.mul_comm]
  omega

/-- For `0 < a < b` the denominators are strictly increasing, hence distinct. -/
theorem greedy_strictly_increasing :
    ∀ a b : ℕ, a < b → (greedy a b).Pairwise (· < ·)
  | 0, b, _ => by simp
  | a + 1, b, hab => by
    rw [greedy_succ]
    set n := (b + a) / (a + 1) with hn_def
    have hb := (ceil_bounds a b).1
    have hup := (ceil_bounds a b).2
    rw [← hn_def] at hb hup
    have hn : 0 < n := Nat.div_pos (by omega) (Nat.succ_pos a)
    set a' := (a + 1) * n - b with ha'_def
    have ha' : a' ≤ a := by rw [ha'_def, Nat.mul_comm]; omega
    have ha'b : a' < n * b := by
      calc a' < b := by omega
        _ ≤ n * b := Nat.le_mul_of_pos_left b hn
    refine List.Pairwise.cons ?_ (greedy_strictly_increasing a' (n * b) ha'b)
    intro m hm
    have hmul := le_mul_of_mem_greedy a' (n * b) m hm
    -- `a' > 0` because `greedy 0 _` is empty
    have ha'pos : 0 < a' := by
      rcases Nat.eq_zero_or_pos a' with h | h
      · rw [h, greedy_zero] at hm; simp at hm
      · exact h
    by_contra hmn
    push Not at hmn
    -- m ≤ n gives m * a' ≤ n * a' < n * b ≤ m * a'
    have h1 : m * a' ≤ n * a' := Nat.mul_le_mul_right a' hmn
    have h2 : n * a' < n * b := Nat.mul_lt_mul_of_pos_left (by omega) hn
    omega
termination_by a => a
decreasing_by
  rw [Nat.mul_comm]
  omega

/-- **Fibonacci.** Every rational in `(0, 1)` is a sum of at most `q.num` distinct unit
fractions. -/
theorem exists_egyptian (q : ℚ) (h0 : 0 < q) (h1 : q < 1) :
    ∃ l : List ℕ, l.Pairwise (· < ·) ∧ (∀ m ∈ l, 0 < m) ∧
      (l.map (fun m : ℕ => (1 : ℚ) / m)).sum = q ∧ (l.length : ℤ) ≤ q.num := by
  have hnum : 0 < q.num := Rat.num_pos.2 h0
  have hden : 0 < q.den := q.den_pos
  set a := q.num.toNat with ha
  have ha_eq : (a : ℤ) = q.num := Int.toNat_of_nonneg hnum.le
  have hq : q = (a : ℚ) / q.den := by
    rw [show (a : ℚ) = (q.num : ℚ) by exact_mod_cast ha_eq]
    exact (Rat.num_div_den q).symm
  have hab : a < q.den := by
    have : (q.num : ℚ) < q.den := by
      have := Rat.num_div_den q
      have hd : (0 : ℚ) < q.den := by exact_mod_cast hden
      rw [← this] at h1
      rwa [div_lt_one hd] at h1
    have : (a : ℚ) < q.den := by rw [← Int.cast_natCast, ha_eq]; exact this
    exact_mod_cast this
  refine ⟨greedy a q.den, greedy_strictly_increasing a q.den hab,
    greedy_pos a q.den hden, ?_, ?_⟩
  · rw [greedy_sum a q.den hden, ← hq]
  · rw [← ha_eq]; exact_mod_cast greedy_length_le a q.den

/-! The worked example from the write-up: `4 / 13 = 1/4 + 1/18 + 1/468`. -/
example : greedy 4 13 = [4, 18, 468] := by decide +kernel

end Egyptian
