module

public import Maroti.Bound
public import Maroti.Classical.AutBound
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart

/-!
# Order and outer-automorphism bounds for even-characteristic symplectic groups

For a finite simple group `S` satisfying `StatedClassicalModel S .PSp n 2 f`
(`n ≥ 2`, `f ≥ 1`, `(n, 2 ^ f) ≠ (2, 2)`), let `q = 2 ^ f`. Since `q` is even,
`Nat.gcd 2 (q - 1) = 1`. By
`CFSG.LocalAnalysis.ComponentInitial.symplectic_model_outer_two_part_bound` and
`Maroti.card_outerAut_psp_dvd`,

* the order satisfies `Nat.card S = q ^ (n ^ 2) * ∏ j ∈ Icc 1 n, (q ^ (2 * j) - 1) ≤
  q ^ (n * (2 * n + 1))`,
* the outer automorphism order satisfies `Nat.card (OuterAut S) ∣ 2 * f`.

This file proves these order formulas and compares `Nat.card S * (2 * f)` with `Maroti.bound`
at the minimum-degree lower bounds for `PSp(2n, 2^f)`:

* for `PSp(6, 2)` (`n = 3, f = 1`), `Nat.card S * 2 ≤ bound 23`,
* for `PSp(8, 2)` (`n = 4, f = 1`), `Nat.card S * 2 ≤ bound 64`,
* for `PSp(2n, 2)` with `n ≥ 5`, `Nat.card S * 2 ≤ bound (2 ^ (2 * n - 2) - 2 ^ (n - 1))`,
* for `PSp(4, 4)` (`n = 2, f = 2`), `Nat.card S * 4 ≤ bound 25`,
* for `PSp(2n, 2^f)` with `f ≥ 2` and `(n, f) ≠ (2, 2)`,
  `Nat.card S * (2 * f) ≤ bound ((2 ^ f) ^ (2 * n - 2))`.
-/

@[expose] public section

namespace Maroti

open Finset CFSG.Open CFSG.LocalAnalysis.ComponentInitial

section ProductBound

/-- Sum identity `∑ i ∈ Icc 1 n, 2 * i = n * (n + 1)`. -/
theorem sum_two_mul_Icc_symplectic (n : ℕ) : ∑ i ∈ Icc 1 n, 2 * i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

/-- Upper bound `∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1) ≤ q ^ (n * (n + 1))`. -/
theorem prod_pow_two_mul_sub_one_le_symplectic (q n : ℕ) :
    ∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1) ≤ q ^ (n * (n + 1)) := by
  calc ∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1)
      ≤ ∏ i ∈ Icc 1 n, q ^ (2 * i) :=
        Finset.prod_le_prod fun _ _ => Nat.sub_le _ _
    _ = q ^ (∑ i ∈ Icc 1 n, 2 * i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ = q ^ (n * (n + 1)) := by rw [sum_two_mul_Icc_symplectic]

/-- For `1 ≤ f`, `Nat.gcd 2 (2 ^ f - 1) = 1`. -/
theorem gcd_two_two_pow_sub_one {f : ℕ} (hf : 1 ≤ f) :
    Nat.gcd 2 (2 ^ f - 1) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
  have h1 : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
    have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    rw [pow_succ']
    omega
  rw [h1, Nat.gcd_rec, show (2 * (2 ^ k - 1) + 1) % 2 = 1 by omega, Nat.gcd_one_left]

/-- Exact order formula for `PSp(2n, 2^f)`:
`Nat.card S = (2 ^ f) ^ (n ^ 2) * ∏ j ∈ Icc 1 n, ((2 ^ f) ^ (2 * j) - 1)`. -/
theorem card_psp_even_eq {S : Type} [Group S] {n f : ℕ}
    (h : StatedClassicalModel S .PSp n 2 f) :
    Nat.card S = (2 ^ f) ^ (n ^ 2) * ∏ j ∈ Icc 1 n, ((2 ^ f) ^ (2 * j) - 1) := by
  have hord := (symplectic_model_outer_two_part_bound S n 2 f h).1
  have hf : 1 ≤ f := h.1.2.1
  rw [hord, gcd_two_two_pow_sub_one hf, Nat.div_one]

/-- Upper bound `Nat.card S ≤ (2 ^ f) ^ (n * (2 * n + 1))` for `PSp(2n, 2^f)`. -/
theorem card_psp_even_le_pow {S : Type} [Group S] {n f : ℕ}
    (h : StatedClassicalModel S .PSp n 2 f) :
    Nat.card S ≤ (2 ^ f) ^ (n * (2 * n + 1)) := by
  rw [card_psp_even_eq h]
  calc (2 ^ f) ^ (n ^ 2) * ∏ j ∈ Icc 1 n, ((2 ^ f) ^ (2 * j) - 1)
      ≤ (2 ^ f) ^ (n ^ 2) * (2 ^ f) ^ (n * (n + 1)) :=
        Nat.mul_le_mul_left _ (prod_pow_two_mul_sub_one_le_symplectic (2 ^ f) n)
    _ = (2 ^ f) ^ (n ^ 2 + n * (n + 1)) := (pow_add (2 ^ f) _ _).symm
    _ = (2 ^ f) ^ (n * (2 * n + 1)) := by congr 1; ring

/-- For `StatedClassicalModel S .PSp n 2 f`,
`Nat.card S * (2 * f) ≤ 2 * f * (2 ^ f) ^ (n * (2 * n + 1))`. -/
theorem card_mul_outer_le_two_mul_pow_psp_even {S : Type} [Group S] {n f : ℕ}
    (h : StatedClassicalModel S .PSp n 2 f) :
    Nat.card S * (2 * f) ≤ 2 * f * (2 ^ f) ^ (n * (2 * n + 1)) := by
  rw [mul_comm (Nat.card S)]
  exact Nat.mul_le_mul_left (2 * f) (card_psp_even_le_pow h)

end ProductBound

section BoundInequalities

/-- For `1 ≤ f`, `2 * f ≤ 2 ^ f`. -/
private theorem two_mul_le_two_pow {f : ℕ} (hf : 1 ≤ f) : 2 * f ≤ 2 ^ f := by
  induction f, hf using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    calc 2 * (k + 1) = 2 * k + 2 := by ring
      _ ≤ 2 * k + 2 * k := Nat.add_le_add_left (by omega) _
      _ = 2 * (2 * k) := by ring
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := by rw [pow_succ']

/-- For `PSp(6, 2)`, `Nat.card S = 1451520`. -/
theorem card_psp_six_two_eq {S : Type} [Group S]
    (h : StatedClassicalModel S .PSp 3 2 1) :
    Nat.card S = 1451520 := by
  rw [card_psp_even_eq h]
  decide

/-- For `PSp(6, 2)`, `Nat.card S * 2 ≤ bound 23`. -/
theorem card_mul_outer_le_bound_psp_six_two {S : Type} [Group S]
    (h : StatedClassicalModel S .PSp 3 2 1) :
    Nat.card S * 2 ≤ bound 23 := by
  rw [card_psp_six_two_eq h]
  decide

/-- For `PSp(8, 2)`, `Nat.card S = 47377612800`. -/
theorem card_psp_eight_two_eq {S : Type} [Group S]
    (h : StatedClassicalModel S .PSp 4 2 1) :
    Nat.card S = 47377612800 := by
  rw [card_psp_even_eq h]
  decide

/-- For `PSp(8, 2)`, `Nat.card S * 2 ≤ bound 64`. -/
theorem card_mul_outer_le_bound_psp_eight_two {S : Type} [Group S]
    (h : StatedClassicalModel S .PSp 4 2 1) :
    Nat.card S * 2 ≤ bound 64 := by
  rw [card_psp_eight_two_eq h]
  decide

/-- For `PSp(4, 4)`, `Nat.card S = 979200`. -/
theorem card_psp_four_four_eq {S : Type} [Group S]
    (h : StatedClassicalModel S .PSp 2 2 2) :
    Nat.card S = 979200 := by
  rw [card_psp_even_eq h]
  decide

/-- For `PSp(4, 4)`, `Nat.card S * 4 ≤ bound 25`. -/
theorem card_mul_outer_le_bound_psp_four_four {S : Type} [Group S]
    (h : StatedClassicalModel S .PSp 2 2 2) :
    Nat.card S * (2 * 2) ≤ bound 25 := by
  rw [card_psp_four_four_eq h]
  decide

/-- For `2 ≤ n`, `2 ^ (2 * n - 3) ≤ 2 ^ (2 * n - 2) - 2 ^ (n - 1)`. -/
theorem two_pow_sub_three_le_sub_pow {n : ℕ} (hn : 2 ≤ n) :
    2 ^ (2 * n - 3) ≤ 2 ^ (2 * n - 2) - 2 ^ (n - 1) := by
  have h1 : n - 1 ≤ 2 * n - 3 := by omega
  have h2 : 2 ^ (n - 1) ≤ 2 ^ (2 * n - 3) := Nat.pow_le_pow_right (by norm_num) h1
  have h3 : 2 * n - 2 = (2 * n - 3) + 1 := by omega
  rw [h3, pow_succ']
  omega

/-- For `6 ≤ n`, `n * (2 * n + 1) + 1 ≤ (2 * n - 3) ^ 2`. -/
theorem psp_two_exp_le_of_six_le {n : ℕ} (hn : 6 ≤ n) :
    n * (2 * n + 1) + 1 ≤ (2 * n - 3) ^ 2 := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 6 := ⟨n - 6, by omega⟩
  have hsub : 2 * (d + 6) - 3 = 2 * d + 9 := by omega
  rw [hsub]
  have hid : (2 * d + 9) ^ 2 =
      ((d + 6) * (2 * (d + 6) + 1) + 1) + (2 * d ^ 2 + 11 * d + 2) := by ring
  rw [hid]
  exact Nat.le_add_right _ _

/-- For `5 ≤ n`, `2 * 2 ^ (n * (2 * n + 1)) ≤ bound (2 ^ (2 * n - 2) - 2 ^ (n - 1))`. -/
theorem two_mul_pow_le_bound_psp_two_of_five_le {n : ℕ} (hn : 5 ≤ n) :
    2 * 2 ^ (n * (2 * n + 1)) ≤ bound (2 ^ (2 * n - 2) - 2 ^ (n - 1)) := by
  by_cases hn5 : n = 5
  · subst hn5; decide
  have hn6 : 6 ≤ n := by omega
  set a := 2 * n - 3
  have hlog : Nat.log 2 (2 ^ a) = a := Nat.log_pow (by norm_num : 1 < 2) a
  have h1 : 2 * 2 ^ (n * (2 * n + 1)) ≤ bound (2 ^ a) := by
    calc 2 * 2 ^ (n * (2 * n + 1))
        = 2 ^ (n * (2 * n + 1) + 1) := (pow_succ' 2 _).symm
      _ ≤ 2 ^ (a ^ 2) := Nat.pow_le_pow_right (by norm_num) (psp_two_exp_le_of_six_le hn6)
      _ = (2 ^ a) ^ a := by rw [sq, pow_mul]
      _ = (2 ^ a) ^ Nat.log 2 (2 ^ a) := by rw [hlog]
      _ ≤ bound (2 ^ a) := pow_log_le_bound (Nat.pow_pos (by norm_num))
  exact h1.trans (bound_mono (two_pow_sub_three_le_sub_pow (by omega)))

/-- For `PSp(2n, 2)` with `5 ≤ n`,
`Nat.card S * 2 ≤ bound (2 ^ (2 * n - 2) - 2 ^ (n - 1))`. -/
theorem card_mul_outer_le_bound_psp_two_of_five_le {S : Type} [Group S] {n : ℕ}
    (h : StatedClassicalModel S .PSp n 2 1) (hn : 5 ≤ n) :
    Nat.card S * (2 * 1) ≤ bound (2 ^ (2 * n - 2) - 2 ^ (n - 1)) := by
  refine (card_mul_outer_le_two_mul_pow_psp_even h).trans ?_
  rw [pow_one]
  exact two_mul_pow_le_bound_psp_two_of_five_le hn

/-- For `2 ≤ n`, `2 ≤ f`, and `¬(n = 2 ∧ f = 2)`,
`f * (n * (2 * n + 1) + 1) ≤ (f * (2 * n - 2)) ^ 2`. -/
theorem psp_even_exp_le_of_two_le_f {n f : ℕ} (hn : 2 ≤ n) (hf : 2 ≤ f)
    (hne : ¬(n = 2 ∧ f = 2)) :
    f * (n * (2 * n + 1) + 1) ≤ (f * (2 * n - 2)) ^ 2 := by
  by_cases hn2 : n = 2
  · subst hn2
    have hf3 : 3 ≤ f := by omega
    obtain ⟨e, rfl⟩ : ∃ e, f = e + 3 := ⟨f - 3, by omega⟩
    change (e + 3) * 11 ≤ ((e + 3) * 2) ^ 2
    have hid : ((e + 3) * 2) ^ 2 = (e + 3) * 11 + (4 * e ^ 2 + 13 * e + 3) := by ring
    rw [hid]
    exact Nat.le_add_right _ _
  · have hn3 : 3 ≤ n := by omega
    obtain ⟨d, rfl⟩ : ∃ d, n = d + 3 := ⟨n - 3, by omega⟩
    obtain ⟨e, rfl⟩ : ∃ e, f = e + 2 := ⟨f - 2, by omega⟩
    have hsub : 2 * (d + 3) - 2 = 2 * d + 4 := by omega
    rw [hsub]
    have hid : ((e + 2) * (2 * d + 4)) ^ 2 =
        (e + 2) * ((d + 3) * (2 * (d + 3) + 1) + 1) +
          ((e + 2) * (4 * d ^ 2 * e + 6 * d ^ 2 + 16 * d * e + 19 * d + 16 * e + 10)) := by ring
    rw [hid]
    exact Nat.le_add_right _ _

/-- For `2 ≤ n`, `2 ≤ f`, and `¬(n = 2 ∧ f = 2)`,
`2 * f * (2 ^ f) ^ (n * (2 * n + 1)) ≤ bound ((2 ^ f) ^ (2 * n - 2))`. -/
theorem two_mul_pow_le_bound_psp_even_of_two_le_f {n f : ℕ} (hn : 2 ≤ n) (hf : 2 ≤ f)
    (hne : ¬(n = 2 ∧ f = 2)) :
    2 * f * (2 ^ f) ^ (n * (2 * n + 1)) ≤ bound ((2 ^ f) ^ (2 * n - 2)) := by
  set a := f * (2 * n - 2)
  have hm : (2 ^ f) ^ (2 * n - 2) = 2 ^ a := (pow_mul 2 f (2 * n - 2)).symm
  have hlog : Nat.log 2 (2 ^ a) = a := Nat.log_pow (by norm_num : 1 < 2) a
  rw [hm]
  calc 2 * f * (2 ^ f) ^ (n * (2 * n + 1))
      ≤ 2 ^ f * (2 ^ f) ^ (n * (2 * n + 1)) :=
        Nat.mul_le_mul_right _ (two_mul_le_two_pow (by omega))
    _ = (2 ^ f) ^ (n * (2 * n + 1) + 1) := (pow_succ' (2 ^ f) _).symm
    _ = 2 ^ (f * (n * (2 * n + 1) + 1)) := (pow_mul 2 f _).symm
    _ ≤ 2 ^ (a ^ 2) :=
        Nat.pow_le_pow_right (by norm_num) (psp_even_exp_le_of_two_le_f hn hf hne)
    _ = (2 ^ a) ^ a := by rw [sq, pow_mul]
    _ = (2 ^ a) ^ Nat.log 2 (2 ^ a) := by rw [hlog]
    _ ≤ bound (2 ^ a) := pow_log_le_bound (Nat.pow_pos (by norm_num))

/-- For `PSp(2n, 2^f)` with `2 ≤ f` and `¬(n = 2 ∧ f = 2)`,
`Nat.card S * (2 * f) ≤ bound ((2 ^ f) ^ (2 * n - 2))`. -/
theorem card_mul_outer_le_bound_psp_even_of_two_le_f {S : Type} [Group S] {n f : ℕ}
    (h : StatedClassicalModel S .PSp n 2 f) (hf : 2 ≤ f) (hne : ¬(n = 2 ∧ f = 2)) :
    Nat.card S * (2 * f) ≤ bound ((2 ^ f) ^ (2 * n - 2)) :=
  (card_mul_outer_le_two_mul_pow_psp_even h).trans
    (two_mul_pow_le_bound_psp_even_of_two_le_f h.1.2.2.1 hf hne)

end BoundInequalities

end Maroti
