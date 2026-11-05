module

public import Maroti.Bound
public import Maroti.Classical.AutBound

/-!
# Order and Outer-Automorphism Bounds for Projective Symplectic Groups in Odd Characteristic

This file proves `Maroti.card_mul_outer_le_bound_psp_odd` and `Maroti.symplecticCase_of_parity`
(Maróti, Section 2, Step 2, page 634).

For a finite simple symplectic group `S` satisfying `StatedClassicalModel S .PSp n p f`
(`n ≥ 2`, `p` prime, `f ≥ 1`), let `q = p ^ f`. By
`CFSG.LocalAnalysis.ComponentInitial.symplectic_model_outer_two_part_bound`
(`CFSG/LocalAnalysis/ComponentInitial/SymplecticModelOuterTwoPart.lean`) and
`Maroti.card_outerAut_psp_dvd`, the order of `S` equals
`q ^ (n ^ 2) * (∏ j ∈ Icc 1 n, (q ^ (2 * j) - 1)) / Nat.gcd 2 (q - 1)` and the outer automorphism
order divides `2 * f * Nat.gcd 2 (q - 1)`. Since
`∏ j ∈ Icc 1 n, (q ^ (2 * j) - 1) ≤ q ^ (n * (n + 1))`
and `2 * f ≤ q`, the product `Nat.card S * (2 * f * Nat.gcd 2 (q - 1))` is at most
`q ^ (n * (2 * n + 1) + 1)`. When `p ≠ 2`, comparing with `Maroti.bound (p * q ^ (2 * n - 2))`
proves `Nat.card S * (2 * f * Nat.gcd 2 (q - 1)) ≤ bound (p * q ^ (2 * n - 2))` for all `n ≥ 2`,
`p ≥ 3`, and `f ≥ 1`.
-/

@[expose] public section

namespace Maroti

open Finset CFSG.Open CFSG.LocalAnalysis.ComponentInitial

section ProductBound

/-- For `StatedClassicalModel S .PSp n p f`,
`Nat.card S * Nat.gcd 2 (p ^ f - 1) ≤ (p ^ f) ^ (n * (2 * n + 1))`. -/
theorem card_mul_gcd_le_pow_psp {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSp n p f) :
    Nat.card S * Nat.gcd 2 (p ^ f - 1) ≤ (p ^ f) ^ (n * (2 * n + 1)) := by
  have hord := (symplectic_model_outer_two_part_bound S n p f h).1
  set q := p ^ f
  rw [hord]
  calc q ^ (n ^ 2) * (∏ j ∈ Icc 1 n, (q ^ (2 * j) - 1)) / Nat.gcd 2 (q - 1) * Nat.gcd 2 (q - 1)
      ≤ q ^ (n ^ 2) * ∏ j ∈ Icc 1 n, (q ^ (2 * j) - 1) := Nat.div_mul_le_self _ _
    _ ≤ q ^ (n ^ 2) * q ^ (n * (n + 1)) :=
        Nat.mul_le_mul_left _ (prod_pow_two_mul_sub_one_le q n)
    _ = q ^ (n ^ 2 + n * (n + 1)) := (pow_add q _ _).symm
    _ = q ^ (n * (2 * n + 1)) := by congr 1; ring

/-- For `StatedClassicalModel S .PSp n p f`,
`Nat.card S * (2 * f * Nat.gcd 2 (p ^ f - 1)) ≤ (p ^ f) ^ (n * (2 * n + 1) + 1)`. -/
theorem card_mul_outer_le_pow_psp {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSp n p f) :
    Nat.card S * (2 * f * Nat.gcd 2 (p ^ f - 1)) ≤ (p ^ f) ^ (n * (2 * n + 1) + 1) := by
  obtain ⟨hp, hf, _, _⟩ := h.1
  set q := p ^ f
  have h2f : 2 * f ≤ q := two_mul_le_pow_of_two_le hp.two_le hf
  calc Nat.card S * (2 * f * Nat.gcd 2 (q - 1))
      = (Nat.card S * Nat.gcd 2 (q - 1)) * (2 * f) := by ring
    _ ≤ q ^ (n * (2 * n + 1)) * q := Nat.mul_le_mul (card_mul_gcd_le_pow_psp h) h2f
    _ = q ^ (n * (2 * n + 1) + 1) := (pow_succ q _).symm

end ProductBound

section BoundInequalities

/-- For `3 ≤ n` and `1 ≤ f`,
`f * (n * (2 * n + 1) + 1) ≤ (f * (2 * n - 2) + 1) * (f * (2 * n - 2) + 3)`. -/
theorem psp_odd_exp_le_of_three_le {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f) :
    f * (n * (2 * n + 1) + 1) ≤ (f * (2 * n - 2) + 1) * (f * (2 * n - 2) + 1 + 2) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 3 := ⟨n - 3, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, f = e + 1 := ⟨f - 1, by omega⟩
  have hsub : 2 * (d + 3) - 2 = 2 * d + 4 := by omega
  rw [hsub]
  have hid : ((e + 1) * (2 * d + 4) + 1) * ((e + 1) * (2 * d + 4) + 1 + 2) =
      (e + 1) * ((d + 3) * (2 * (d + 3) + 1) + 1) +
        (4 * d ^ 2 * e ^ 2 + 6 * d ^ 2 * e + 2 * d ^ 2 + 16 * d * e ^ 2 + 27 * d * e + 11 * d +
          16 * e ^ 2 + 26 * e + 13) := by ring
  rw [hid]
  exact Nat.le_add_right _ _

/-- For `3 ≤ n`, `3 ≤ p`, and `1 ≤ f`,
`(p ^ f) ^ (n * (2 * n + 1) + 1) ≤ bound (p * (p ^ f) ^ (2 * n - 2))`. -/
theorem pow_le_bound_psp_odd_of_three_le {n p f : ℕ} (hn : 3 ≤ n) (hp : 3 ≤ p) (hf : 1 ≤ f) :
    (p ^ f) ^ (n * (2 * n + 1) + 1) ≤ bound (p * (p ^ f) ^ (2 * n - 2)) := by
  set a := f * (2 * n - 2) + 1
  have hm : p * (p ^ f) ^ (2 * n - 2) = p ^ a := by
    rw [← pow_mul, ← pow_succ']
  have ha4 : 4 ≤ a := by
    have : 4 ≤ 2 * n - 2 := by omega
    have : 4 ≤ f * (2 * n - 2) := le_trans (by omega) (Nat.mul_le_mul hf this)
    omega
  have hp0 : 0 < p := by omega
  have hpa0 : 0 < p ^ a := Nat.pow_pos hp0
  rw [hm, ← pow_mul]
  calc p ^ (f * (n * (2 * n + 1) + 1))
      ≤ p ^ (a * (a + 2)) := Nat.pow_le_pow_right hp0 (psp_odd_exp_le_of_three_le hn hf)
    _ ≤ p ^ (a * Nat.log 2 (p ^ a)) :=
        Nat.pow_le_pow_right hp0 (Nat.mul_le_mul_left a (add_two_le_log_of_three_le hp ha4))
    _ = (p ^ a) ^ Nat.log 2 (p ^ a) := by rw [pow_mul]
    _ ≤ bound (p ^ a) := pow_log_le_bound hpa0

/-- For `n = 2`, `3 ≤ p`, and `2 ≤ f`,
`(p ^ f) ^ 11 ≤ bound (p * (p ^ f) ^ 2)`. -/
theorem pow_le_bound_psp_odd_two_of_two_le_f {p f : ℕ} (hp : 3 ≤ p) (hf : 2 ≤ f) :
    (p ^ f) ^ 11 ≤ bound (p * (p ^ f) ^ 2) := by
  set a := f * 2 + 1
  have hm : p * (p ^ f) ^ 2 = p ^ a := by
    rw [← pow_mul, ← pow_succ']
  have ha4 : 4 ≤ a := by omega
  have hexp : f * 11 ≤ a * (a + 2) := by
    obtain ⟨e, rfl⟩ : ∃ e, f = e + 2 := ⟨f - 2, by omega⟩
    change (e + 2) * 11 ≤ ((e + 2) * 2 + 1) * ((e + 2) * 2 + 1 + 2)
    have hid : ((e + 2) * 2 + 1) * ((e + 2) * 2 + 1 + 2) =
        (e + 2) * 11 + (4 * e ^ 2 + 13 * e + 13) := by ring
    rw [hid]
    exact Nat.le_add_right _ _
  have hp0 : 0 < p := by omega
  have hpa0 : 0 < p ^ a := Nat.pow_pos hp0
  rw [hm, ← pow_mul]
  calc p ^ (f * 11)
      ≤ p ^ (a * (a + 2)) := Nat.pow_le_pow_right hp0 hexp
    _ ≤ p ^ (a * Nat.log 2 (p ^ a)) :=
        Nat.pow_le_pow_right hp0 (Nat.mul_le_mul_left a (add_two_le_log_of_three_le hp ha4))
    _ = (p ^ a) ^ Nat.log 2 (p ^ a) := by rw [pow_mul]
    _ ≤ bound (p ^ a) := pow_log_le_bound hpa0

/-- For `n = 2`, `5 ≤ p`, and `f = 1`, `p ^ 11 ≤ bound (p * p ^ 2)`. -/
theorem pow_le_bound_psp_odd_two_one_of_five_le {p : ℕ} (hp : 5 ≤ p) :
    p ^ 11 ≤ bound (p * p ^ 2) := by
  have hm : p * p ^ 2 = p ^ 3 := by ring
  have hlog : 6 ≤ Nat.log 2 (p ^ 3) := by
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    calc 2 ^ 6 ≤ 5 ^ 3 := by decide
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp 3
  have hp0 : 0 < p := by omega
  have hpa0 : 0 < p ^ 3 := Nat.pow_pos hp0
  rw [hm]
  calc p ^ 11
      ≤ p ^ (3 * 6) := Nat.pow_le_pow_right hp0 (by norm_num)
    _ ≤ p ^ (3 * Nat.log 2 (p ^ 3)) :=
        Nat.pow_le_pow_right hp0 (Nat.mul_le_mul_left 3 hlog)
    _ = (p ^ 3) ^ Nat.log 2 (p ^ 3) := by rw [pow_mul]
    _ ≤ bound (p ^ 3) := pow_log_le_bound hpa0

/-- Maróti's numerical bound for `PSp(2n, p ^ f)` with `p` odd (`n ≥ 2`, `p ≠ 2`, `f ≥ 1`):
`Nat.card S * (2 * f * Nat.gcd 2 (p ^ f - 1)) ≤ bound (p * (p ^ f) ^ (2 * n - 2))`. -/
theorem card_mul_outer_le_bound_psp_odd {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSp n p f) (hp2 : p ≠ 2) :
    Nat.card S * (2 * f * Nat.gcd 2 (p ^ f - 1)) ≤ bound (p * (p ^ f) ^ (2 * n - 2)) := by
  obtain ⟨hp, hf, hn, _⟩ := h.1
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  by_cases hn3 : 3 ≤ n
  · exact (card_mul_outer_le_pow_psp h).trans (pow_le_bound_psp_odd_of_three_le hn3 hp3 hf)
  · have hn2 : n = 2 := by omega
    subst hn2
    by_cases hf2 : 2 ≤ f
    · exact (card_mul_outer_le_pow_psp h).trans (pow_le_bound_psp_odd_two_of_two_le_f hp3 hf2)
    · have hf1 : f = 1 := by omega
      subst hf1
      by_cases hp3_eq : p = 3
      · subst hp3_eq
        have hord := (symplectic_model_outer_two_part_bound S 2 3 1 h).1
        rw [hord]
        decide
      · have hp5 : 5 ≤ p := by
          have hp4 : p ≠ 4 := fun h4 => by subst h4; exact absurd hp (by decide)
          omega
        exact (card_mul_outer_le_pow_psp h).trans
          (by simpa using pow_le_bound_psp_odd_two_one_of_five_le hp5)

/-- Theorem 1.1 for almost simple groups with socle `PSp(2n, q)` follows from the odd-`q` and
even-`q` cases by splitting on whether `p = 2`. -/
theorem symplecticCase_of_parity (hOdd : AlmostSimpleCase SymplecticSocleOdd)
    (hEven : AlmostSimpleCase SymplecticSocleEven) : AlmostSimpleCase (ClassicalSocle .PSp) := by
  intro α _ G S _ hPrim hAS ⟨n, p, f, hModel⟩
  by_cases hp : p = 2
  · exact hEven α G S hPrim hAS ⟨n, f, hp ▸ hModel⟩
  · exact hOdd α G S hPrim hAS ⟨n, p, f, hp, hModel⟩

end BoundInequalities

end Maroti
