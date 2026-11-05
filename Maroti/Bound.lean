module

public import Maroti.Statement
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Log

/-!
# Properties of Maróti's bound

This file proves the arithmetic inequalities for the order bound
`Maroti.bound n = n · ∏_{i < ⌊log₂ n⌋} (n - 2^i)` from Section 2 of A. Maróti,
*On the orders of primitive groups*, J. Algebra 258 (2002), pages 633–634.

Each factor `n - 2^i` with `i < ⌊log₂ n⌋` lies between `n / 2` and `n`.
Multiplying these bounds over the `⌊log₂ n⌋` factors shows that `bound` is strictly increasing
(`bound_strictMono`, `bound_mono`) and satisfies the sandwich inequalities
`n ^ ⌊log₂ n⌋ ≤ bound n < n ^ (1 + ⌊log₂ n⌋)` (`pow_log_le_bound`, `bound_lt_pow`).
Combining `k! ≤ 4^(k(k-1))` with `pow_log_le_bound` gives the wreath product and diagonal
inequalities `k! · (bound m)^k ≤ bound (m^k)` (`factorial_mul_bound_pow_le`),
`k! · H^k ≤ bound (m^k)` (`factorial_mul_pow_le_bound_of_mathieu`), and
`k! · t^(2k) ≤ bound (t^⌈k/2⌉)` (`diagonal_bound_le`) used in Step 1 of Theorem 1.1.
-/

@[expose] public section

namespace Maroti

@[simp]
theorem bound_zero : bound 0 = 0 := by
  simp [bound]

@[simp]
theorem bound_one : bound 1 = 1 := by
  simp [bound]

@[simp]
theorem bound_two : bound 2 = 2 := by
  decide

theorem two_mul_two_pow_le_of_lt_log {n i : ℕ} (hi : i < Nat.log 2 n) :
    2 * 2 ^ i ≤ n := by
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hi
  calc 2 * 2 ^ i = 2 ^ (i + 1) := by rw [pow_succ']
    _ ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by omega) hi
    _ ≤ n := Nat.pow_log_le_self 2 hn

theorem two_pow_lt_of_lt_log {n i : ℕ} (hi : i < Nat.log 2 n) : 2 ^ i < n := by
  have h := two_mul_two_pow_le_of_lt_log hi
  have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
  omega

theorem sub_two_pow_pos {n i : ℕ} (hi : i < Nat.log 2 n) : 0 < n - 2 ^ i := by
  have h := two_pow_lt_of_lt_log hi
  omega

theorem le_two_mul_sub_two_pow {n i : ℕ} (hi : i < Nat.log 2 n) : n ≤ 2 * (n - 2 ^ i) := by
  have h := two_mul_two_pow_le_of_lt_log hi
  omega

theorem one_le_prod_sub_two_pow (n : ℕ) :
    1 ≤ ∏ i ∈ Finset.range (Nat.log 2 n), (n - 2 ^ i) := by
  apply Finset.one_le_prod
  intro i hi
  exact sub_two_pow_pos (Finset.mem_range.mp hi)

theorem bound_pos {n : ℕ} (hn : 0 < n) : 0 < bound n := by
  unfold bound
  exact Nat.mul_pos hn (one_le_prod_sub_two_pow n)

theorem self_le_bound (n : ℕ) : n ≤ bound n := by
  unfold bound
  exact Nat.le_mul_of_pos_right n (one_le_prod_sub_two_pow n)

theorem bound_lt_succ (n : ℕ) : bound n < bound (n + 1) := by
  unfold bound
  have hlog : Nat.log 2 n ≤ Nat.log 2 (n + 1) := Nat.log_mono_right (Nat.le_succ n)
  have hprod1 : ∏ i ∈ Finset.range (Nat.log 2 n), (n - 2 ^ i) ≤
      ∏ i ∈ Finset.range (Nat.log 2 n), (n + 1 - 2 ^ i) := by
    apply Finset.prod_le_prod
    intro i _
    omega
  have hprod2 : ∏ i ∈ Finset.range (Nat.log 2 n), (n + 1 - 2 ^ i) ≤
      ∏ i ∈ Finset.range (Nat.log 2 (n + 1)), (n + 1 - 2 ^ i) := by
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.range_mono hlog)
    intro i hi _
    exact sub_two_pow_pos (Finset.mem_range.mp hi)
  have hprod : ∏ i ∈ Finset.range (Nat.log 2 n), (n - 2 ^ i) ≤
      ∏ i ∈ Finset.range (Nat.log 2 (n + 1)), (n + 1 - 2 ^ i) :=
    hprod1.trans hprod2
  have hpos : 0 < ∏ i ∈ Finset.range (Nat.log 2 (n + 1)), (n + 1 - 2 ^ i) :=
    one_le_prod_sub_two_pow (n + 1)
  calc n * ∏ i ∈ Finset.range (Nat.log 2 n), (n - 2 ^ i)
      ≤ n * ∏ i ∈ Finset.range (Nat.log 2 (n + 1)), (n + 1 - 2 ^ i) :=
        Nat.mul_le_mul_left n hprod
    _ < (n + 1) * ∏ i ∈ Finset.range (Nat.log 2 (n + 1)), (n + 1 - 2 ^ i) :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self n) hpos

/-- The function `Maroti.bound` is strictly increasing (Maróti, Section 2, page 633). -/
theorem bound_strictMono : StrictMono bound :=
  strictMono_nat_of_lt_succ bound_lt_succ

/-- The function `Maroti.bound` is monotone (Maróti, Section 2, page 633). -/
theorem bound_mono : Monotone bound :=
  bound_strictMono.monotone

/-- For every positive `n`, we have `n ^ ⌊log₂ n⌋ ≤ bound n` (Maróti, Section 2, page 633). -/
theorem pow_log_le_bound {n : ℕ} (hn : 0 < n) : n ^ Nat.log 2 n ≤ bound n := by
  unfold bound
  have h1 : ∏ i ∈ Finset.range (Nat.log 2 n), n ≤
      ∏ i ∈ Finset.range (Nat.log 2 n), (2 * (n - 2 ^ i)) := by
    apply Finset.prod_le_prod
    intro i hi
    exact le_two_mul_sub_two_pow (Finset.mem_range.mp hi)
  rw [Finset.prod_const, Finset.card_range, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range] at h1
  have h2 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
  exact h1.trans (Nat.mul_le_mul_right _ h2)

/-- For every `n`, we have `bound n ≤ n ^ (1 + ⌊log₂ n⌋)` (Maróti, Section 2, page 633). -/
theorem bound_le_pow (n : ℕ) : bound n ≤ n ^ (1 + Nat.log 2 n) := by
  unfold bound
  rw [pow_add, pow_one]
  apply Nat.mul_le_mul_left
  calc ∏ i ∈ Finset.range (Nat.log 2 n), (n - 2 ^ i)
      ≤ ∏ _i ∈ Finset.range (Nat.log 2 n), n := by
        apply Finset.prod_le_prod
        intro i _
        exact Nat.sub_le n (2 ^ i)
    _ = n ^ Nat.log 2 n := by rw [Finset.prod_const, Finset.card_range]

/-- For `n ≥ 2`, we have `bound n < n ^ (1 + ⌊log₂ n⌋)` (Maróti, Section 2, page 633). -/
theorem bound_lt_pow {n : ℕ} (hn : 2 ≤ n) : bound n < n ^ (1 + Nat.log 2 n) := by
  unfold bound
  rw [pow_add, pow_one]
  have hd : 1 ≤ Nat.log 2 n := Nat.log_pos (by omega) hn
  obtain ⟨k, hk⟩ : ∃ k, Nat.log 2 n = k + 1 := Nat.exists_eq_add_of_le' hd
  rw [hk, Finset.prod_range_succ', pow_zero, pow_succ]
  have hprod : ∏ i ∈ Finset.range k, (n - 2 ^ (i + 1)) ≤ n ^ k := by
    calc ∏ i ∈ Finset.range k, (n - 2 ^ (i + 1))
        ≤ ∏ _i ∈ Finset.range k, n := by
          apply Finset.prod_le_prod
          intro i _
          exact Nat.sub_le n _
      _ = n ^ k := by rw [Finset.prod_const, Finset.card_range]
  have hlt : (∏ i ∈ Finset.range k, (n - 2 ^ (i + 1))) * (n - 1) < n ^ k * n := by
    calc (∏ i ∈ Finset.range k, (n - 2 ^ (i + 1))) * (n - 1)
        ≤ n ^ k * (n - 1) := Nat.mul_le_mul_right (n - 1) hprod
      _ < n ^ k * n := Nat.mul_lt_mul_of_pos_left (by omega) (Nat.pow_pos (by omega))
  exact Nat.mul_lt_mul_of_pos_left hlt (by omega)

theorem le_four_pow_sub_one {k : ℕ} (hk : 2 ≤ k) : k ≤ 4 ^ (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  clear hk
  induction m with
  | zero => decide
  | succ m ih =>
    calc m + 1 + 2 ≤ 4 * (m + 2) := by omega
      _ ≤ 4 * 4 ^ (m + 2 - 1) := Nat.mul_le_mul_left 4 ih
      _ = 4 ^ (m + 1 + 2 - 1) := by rw [← pow_succ']; rfl

theorem factorial_le_pow_mul_sub_one {m k : ℕ} (hm : 4 ≤ m) (hk : 2 ≤ k) :
    k.factorial ≤ m ^ (k * (k - 1)) := by
  have hk4 : k ≤ m ^ (k - 1) :=
    (le_four_pow_sub_one hk).trans (Nat.pow_le_pow_left hm (k - 1))
  calc k.factorial ≤ k ^ k := Nat.factorial_le_pow k
    _ ≤ (m ^ (k - 1)) ^ k := Nat.pow_le_pow_left hk4 k
    _ = m ^ (k * (k - 1)) := by rw [← pow_mul, mul_comm]

theorem mul_log_le_log_pow {m : ℕ} (hm : 0 < m) (k : ℕ) :
    k * Nat.log 2 m ≤ Nat.log 2 (m ^ k) := by
  apply Nat.le_log_of_pow_le (by omega)
  rw [mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (Nat.ne_of_gt hm)) k

theorem factorial_mul_pow_le_bound_pow {m k a : ℕ} (hm : 4 ≤ m) (hk : 2 ≤ k)
    (ha : k - 1 + a ≤ k * Nat.log 2 m) :
    k.factorial * (m ^ a) ^ k ≤ bound (m ^ k) := by
  have hm0 : 0 < m := by omega
  have hmk0 : 0 < m ^ k := Nat.pow_pos hm0
  calc k.factorial * (m ^ a) ^ k
      ≤ m ^ (k * (k - 1)) * m ^ (k * a) := by
        rw [← pow_mul, mul_comm a k]
        exact Nat.mul_le_mul_right _ (factorial_le_pow_mul_sub_one hm hk)
    _ = m ^ (k * (k - 1 + a)) := by rw [← pow_add, ← mul_add]
    _ ≤ m ^ (k * (k * Nat.log 2 m)) :=
        Nat.pow_le_pow_right hm0 (Nat.mul_le_mul_left k ha)
    _ = (m ^ k) ^ (k * Nat.log 2 m) := by rw [pow_mul]
    _ ≤ (m ^ k) ^ Nat.log 2 (m ^ k) :=
        Nat.pow_le_pow_right hmk0 (mul_log_le_log_pow hm0 k)
    _ ≤ bound (m ^ k) := pow_log_le_bound hmk0

/-- For `m ≥ 4` and `k ≥ 2`, we have `k! · (bound m)^k ≤ bound (m^k)`
(Maróti, Section 2, Step 1, page 633). -/
theorem factorial_mul_bound_pow_le {m k : ℕ} (hm : 4 ≤ m) (hk : 2 ≤ k) :
    k.factorial * bound m ^ k ≤ bound (m ^ k) := by
  have hd : 2 ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by omega) hm
  have ha : k - 1 + (1 + Nat.log 2 m) ≤ k * Nat.log 2 m := by
    have : 2 * Nat.log 2 m ≤ k * Nat.log 2 m := Nat.mul_le_mul_right _ hk
    have : k * 2 ≤ k * Nat.log 2 m := Nat.mul_le_mul_left k hd
    omega
  calc k.factorial * bound m ^ k
      ≤ k.factorial * (m ^ (1 + Nat.log 2 m)) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (bound_le_pow m) k)
    _ ≤ bound (m ^ k) := factorial_mul_pow_le_bound_pow hm hk ha

/-- Product-type bound when the factor group `H` has order at most `m ^ (2 ⌊log₂ m⌋ - 1)` for
`m ≥ 8` and `k ≥ 2`, covering the four 4-transitive Mathieu groups
(Maróti, Section 2, Step 1, page 633). -/
theorem factorial_mul_pow_le_bound_of_mathieu {m k H : ℕ} (hm : 8 ≤ m) (hk : 2 ≤ k)
    (hH : H ≤ m ^ (2 * Nat.log 2 m - 1)) :
    k.factorial * H ^ k ≤ bound (m ^ k) := by
  have hd : 3 ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by omega) hm
  have ha : k - 1 + (2 * Nat.log 2 m - 1) ≤ k * Nat.log 2 m := by
    have : (k - 2) * 3 ≤ (k - 2) * Nat.log 2 m := Nat.mul_le_mul_left (k - 2) hd
    have : (k - 2) * Nat.log 2 m + 2 * Nat.log 2 m = k * Nat.log 2 m := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hk]
    omega
  calc k.factorial * H ^ k
      ≤ k.factorial * (m ^ (2 * Nat.log 2 m - 1)) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hH k)
    _ ≤ bound (m ^ k) := factorial_mul_pow_le_bound_pow (by omega) hk ha

/-- Diagonal-type bound: for `t ≥ 32` and `k ≥ 2`, we have `k! · t^(2k) ≤ bound (t^⌈k/2⌉)`
(Maróti, Section 2, Step 1, pages 633–634). -/
theorem diagonal_bound_le {t k : ℕ} (ht : 32 ≤ t) (hk : 2 ≤ k) :
    k.factorial * t ^ (2 * k) ≤ bound (t ^ ((k + 1) / 2)) := by
  have ht0 : 0 < t := by omega
  have hd : 5 ≤ Nat.log 2 t := Nat.le_log_of_pow_le (by omega) ht
  set r := (k + 1) / 2
  have htr0 : 0 < t ^ r := Nat.pow_pos ht0
  have hbase : t ^ (r * (r * Nat.log 2 t)) ≤ bound (t ^ r) := by
    calc t ^ (r * (r * Nat.log 2 t))
        = (t ^ r) ^ (r * Nat.log 2 t) := by rw [pow_mul]
      _ ≤ (t ^ r) ^ Nat.log 2 (t ^ r) :=
          Nat.pow_le_pow_right htr0 (mul_log_le_log_pow ht0 r)
      _ ≤ bound (t ^ r) := pow_log_le_bound htr0
  rcases eq_or_lt_of_le hk with rfl | hk3
  · show (2 : ℕ).factorial * t ^ (2 * 2) ≤ bound (t ^ r)
    have hr_eq : r = 1 := rfl
    have h1 : (2 : ℕ).factorial * t ^ (2 * 2) ≤ t ^ 5 := by
      calc 2 * t ^ 4 ≤ t * t ^ 4 := Nat.mul_le_mul_right _ (by omega)
        _ = t ^ 5 := by rw [← pow_succ']
    refine h1.trans ((Nat.pow_le_pow_right ht0 ?_).trans hbase)
    rw [hr_eq, one_mul, one_mul]
    exact hd
  · have hr2 : 2 ≤ r := by omega
    have hk_le : k ≤ 2 * r := by omega
    have hexp : k * (k - 1) + 2 * k ≤ r * (r * Nat.log 2 t) := by
      have h1 : k * (k - 1) + 2 * k = k * (k + 1) := by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
      have h2 : k * (k + 1) ≤ 2 * r * (2 * r + 1) :=
        Nat.mul_le_mul hk_le (Nat.add_le_add_right hk_le 1)
      have h3 : 2 * r * (2 * r + 1) ≤ 5 * (r * r) := by
        have : 2 * r ≤ r * r := Nat.mul_le_mul_right r hr2
        have : 2 * r * (2 * r + 1) = 4 * (r * r) + 2 * r := by ring
        omega
      have h4 : 5 * (r * r) ≤ Nat.log 2 t * (r * r) := Nat.mul_le_mul_right (r * r) hd
      have h5 : Nat.log 2 t * (r * r) = r * (r * Nat.log 2 t) := by ring
      omega
    calc k.factorial * t ^ (2 * k)
        ≤ t ^ (k * (k - 1)) * t ^ (2 * k) :=
          Nat.mul_le_mul_right _ (factorial_le_pow_mul_sub_one (by omega) hk)
      _ = t ^ (k * (k - 1) + 2 * k) := by rw [← pow_add]
      _ ≤ t ^ (r * (r * Nat.log 2 t)) := Nat.pow_le_pow_right ht0 hexp
      _ ≤ bound (t ^ r) := hbase

/-- For any `f ≥ 1` and `p ≥ 2`, `2 * f ≤ p ^ f`. -/
theorem two_mul_le_pow_of_two_le {p f : ℕ} (hp : 2 ≤ p) (hf : 1 ≤ f) :
    2 * f ≤ p ^ f := by
  have h2f : 2 * f ≤ 2 ^ f := by
    induction f, hf using Nat.le_induction with
    | base => decide
    | succ k hk ih =>
      have hk2 : 2 ≤ 2 * k := by omega
      calc 2 * (k + 1) = 2 * k + 2 := by ring
        _ ≤ 2 * k + 2 * k := Nat.add_le_add_left hk2 _
        _ = 2 * (2 * k) := by ring
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1) := by rw [pow_succ']
  exact h2f.trans (Nat.pow_le_pow_left hp f)

/-- The sum `∑ i ∈ Finset.Icc 1 m, 2 * i` equals `m * (m + 1)`. -/
theorem sum_two_mul_Icc (m : ℕ) : ∑ i ∈ Finset.Icc 1 m, 2 * i = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

/-- The product `∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1)` is at most `q ^ (m * (m + 1))`. -/
theorem prod_pow_two_mul_sub_one_le (q m : ℕ) :
    ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) ≤ q ^ (m * (m + 1)) := by
  calc ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1)
      ≤ ∏ i ∈ Finset.Icc 1 m, q ^ (2 * i) :=
        Finset.prod_le_prod fun _ _ => Nat.sub_le _ _
    _ = q ^ (∑ i ∈ Finset.Icc 1 m, 2 * i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ = q ^ (m * (m + 1)) := by rw [sum_two_mul_Icc]

/-- For `4 ≤ a`, `2 ^ (a + 2) ≤ 3 ^ a`. -/
theorem two_pow_add_two_le_three_pow {a : ℕ} (ha : 4 ≤ a) : 2 ^ (a + 2) ≤ 3 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ k _ ih =>
    calc 2 ^ (k + 1 + 2) = 2 * 2 ^ (k + 2) := by rw [pow_succ']
      _ ≤ 3 * 3 ^ k := Nat.mul_le_mul (by decide) ih
      _ = 3 ^ (k + 1) := by rw [pow_succ']

/-- For `3 ≤ p` and `4 ≤ a`, `a + 2 ≤ Nat.log 2 (p ^ a)`. -/
theorem add_two_le_log_of_three_le {p a : ℕ} (hp : 3 ≤ p) (ha : 4 ≤ a) :
    a + 2 ≤ Nat.log 2 (p ^ a) :=
  Nat.le_log_of_pow_le (by decide)
    ((two_pow_add_two_le_three_pow ha).trans (Nat.pow_le_pow_left hp a))

end Maroti
