module

public import Maroti.Bound
public import Maroti.Classical.AutBound
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart

/-!
# Order and Outer-Automorphism Bounds for Projective Special Unitary Groups

This file proves `Maroti.card_mul_outer_le_bound_psu` (Maróti, Section 2, Step 2, page 634).

For a finite simple unitary group `S` satisfying `StatedClassicalModel S .PSU n p f`
(`n ≥ 3`, `p` prime, `f ≥ 1`, `(n, p ^ f) ≠ (3, 2)`), let `q = p ^ f`. By
`CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound`
(`CFSG/LocalAnalysis/ComponentInitial/UnitaryModelOuterTwoPart.lean`) and
`Maroti.card_outerAut_psu_eq`, the order of `S` satisfies
`(Nat.card S : ℤ) * (Nat.gcd n (q + 1) : ℤ) =
  q ^ (n * (n - 1) / 2) * ∏ j ∈ Icc 2 n, (q ^ j - (-1) ^ j)`
and the outer automorphism order equals `2 * f * Nat.gcd n (q + 1)`.

Pairing each even factor `q ^ (2 * m) - 1` with the following odd factor `q ^ (2 * m + 1) + 1` gives
`∏ j ∈ Icc 2 n, (q ^ j - (-1) ^ j) ≤ q ^ (∑ j ∈ Icc 2 n, j)`. Since
`n * (n - 1) / 2 + ∑ j ∈ Icc 2 n, j = n ^ 2 - 1`, we obtain
`Nat.card S * Nat.gcd n (q + 1) ≤ q ^ (n ^ 2 - 1)` and
`Nat.card S * (2 * f * Nat.gcd n (q + 1)) ≤ 2 * f * q ^ (n ^ 2 - 1) ≤ bound (2 * p * q ^ (n - 2))`.
-/

@[expose] public section

namespace Maroti

open Finset CFSG.Open CFSG.LocalAnalysis.ComponentInitial

section ProductBound

/-- For `1 ≤ q` in `ℤ` and `m : ℕ`,
`(q ^ (2 * m) - (-1) ^ (2 * m)) * (q ^ (2 * m + 1) - (-1) ^ (2 * m + 1)) ≤
  q ^ (2 * m + (2 * m + 1))`. -/
theorem even_odd_factor_mul_le {q : ℤ} (hq : 1 ≤ q) (m : ℕ) :
    (q ^ (2 * m) - (-1) ^ (2 * m)) * (q ^ (2 * m + 1) - (-1) ^ (2 * m + 1)) ≤
      q ^ (2 * m + (2 * m + 1)) := by
  have he : (-1 : ℤ) ^ (2 * m) = 1 := Even.neg_one_pow ⟨m, by ring⟩
  have ho : (-1 : ℤ) ^ (2 * m + 1) = -1 := Odd.neg_one_pow ⟨m, rfl⟩
  rw [he, ho, sub_neg_eq_add]
  have hqm : 0 ≤ q ^ (2 * m) := pow_nonneg (by omega) _
  have hq1 : 0 ≤ q - 1 := by omega
  have hnonneg : 0 ≤ q ^ (2 * m) * (q - 1) + 1 :=
    add_nonneg (mul_nonneg hqm hq1) zero_le_one
  have hid : (q ^ (2 * m) - 1) * (q ^ (2 * m + 1) + 1) + (q ^ (2 * m) * (q - 1) + 1) =
      q ^ (2 * m + (2 * m + 1)) := by
    rw [pow_add, pow_succ]
    ring
  linarith

/-- For `q : ℤ` and `m : ℕ`, `q ^ (2 * m) - (-1) ^ (2 * m) ≤ q ^ (2 * m)`. -/
theorem even_factor_le (q : ℤ) (m : ℕ) :
    q ^ (2 * m) - (-1) ^ (2 * m) ≤ q ^ (2 * m) := by
  have he : (-1 : ℤ) ^ (2 * m) = 1 := Even.neg_one_pow ⟨m, by ring⟩
  rw [he]
  omega

/-- Each factor `q ^ j - (-1) ^ j` is nonnegative for `1 ≤ q`. -/
theorem factor_nonneg {q : ℤ} (hq : 1 ≤ q) (j : ℕ) :
    0 ≤ q ^ j - (-1) ^ j := by
  have hqj : 1 ≤ q ^ j := one_le_pow₀ hq
  rcases neg_one_pow_eq_or ℤ j with h1 | h1 <;> rw [h1] <;> omega

/-- For `1 ≤ q` and `1 ≤ k`,
`∏ j ∈ Icc 2 (2 * k + 1), (q ^ j - (-1) ^ j) ≤ q ^ (∑ j ∈ Icc 2 (2 * k + 1), j)`. -/
theorem prod_pow_sub_neg_one_pow_odd_le {q : ℤ} (hq : 1 ≤ q) {k : ℕ} (hk : 1 ≤ k) :
    ∏ j ∈ Icc 2 (2 * k + 1), (q ^ j - (-1) ^ j) ≤
      q ^ (∑ j ∈ Icc 2 (2 * k + 1), j) := by
  induction k, hk using Nat.le_induction with
  | base =>
    have hIcc : Icc 2 3 = insert 2 {3} := by decide
    rw [hIcc, prod_insert (by decide), prod_singleton, sum_insert (by decide), sum_singleton]
    exact even_odd_factor_mul_le hq 1
  | succ m hm ih =>
    have hstep : 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 := by omega
    rw [hstep, prod_Icc_succ_top (by omega), prod_Icc_succ_top (by omega),
      sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega)]
    have h1 : (2 * m + 1) + 1 = 2 * (m + 1) := by omega
    rw [h1, mul_assoc, add_assoc, pow_add q (∑ j ∈ Icc 2 (2 * m + 1), j)]
    exact mul_le_mul ih (even_odd_factor_mul_le hq (m + 1))
      (mul_nonneg (factor_nonneg hq _) (factor_nonneg hq _))
      (pow_nonneg (by omega) _)

/-- For `1 ≤ q` and `3 ≤ n`,
`∏ j ∈ Icc 2 n, (q ^ j - (-1) ^ j) ≤ q ^ (∑ j ∈ Icc 2 n, j)`. -/
theorem prod_pow_sub_neg_one_pow_le {q : ℤ} (hq : 1 ≤ q) {n : ℕ} (hn : 3 ≤ n) :
    ∏ j ∈ Icc 2 n, (q ^ j - (-1) ^ j) ≤ q ^ (∑ j ∈ Icc 2 n, j) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have hk2 : 2 ≤ k := by omega
    have hstep : 2 * k = (2 * (k - 1) + 1) + 1 := by omega
    rw [hstep, prod_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), ← hstep, pow_add]
    exact mul_le_mul (prod_pow_sub_neg_one_pow_odd_le hq (by omega)) (even_factor_le q k)
      (factor_nonneg hq _) (pow_nonneg (by omega) _)
  · exact prod_pow_sub_neg_one_pow_odd_le hq (by omega)

/-- For `2 ≤ n`, `n * (n - 1) / 2 + ∑ j ∈ Icc 2 n, j = n ^ 2 - 1`. -/
theorem half_mul_sub_one_add_sum_Icc {n : ℕ} (hn : 2 ≤ n) :
    n * (n - 1) / 2 + ∑ j ∈ Icc 2 n, j = n ^ 2 - 1 := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hdiv : (m + 1) * m / 2 = m * (m - 1) / 2 + m := by
      have hmul : (m + 1) * m = m * (m - 1) + 2 * m := by
        obtain ⟨d, rfl⟩ : ∃ d, m = d + 2 := ⟨m - 2, by omega⟩
        change (d + 3) * (d + 2) = (d + 2) * (d + 1) + 2 * (d + 2)
        ring
      rw [hmul, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    rw [Nat.add_sub_cancel, hdiv]
    have hsum : m * (m - 1) / 2 + m + (∑ j ∈ Icc 2 m, j + (m + 1)) =
        (m * (m - 1) / 2 + ∑ j ∈ Icc 2 m, j) + (2 * m + 1) := by ring
    rw [hsum, ih]
    obtain ⟨d, rfl⟩ : ∃ d, m = d + 2 := ⟨m - 2, by omega⟩
    zify [show 1 ≤ (d + 2) ^ 2 by nlinarith, show 1 ≤ (d + 2 + 1) ^ 2 by nlinarith]
    ring

/-- For `StatedClassicalModel S .PSU n p f`,
`Nat.card S * Nat.gcd n (p ^ f + 1) ≤ (p ^ f) ^ (n ^ 2 - 1)`. -/
theorem card_mul_gcd_le_pow_psu {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSU n p f) :
    Nat.card S * Nat.gcd n (p ^ f + 1) ≤ (p ^ f) ^ (n ^ 2 - 1) := by
  obtain ⟨hp, hf, hn, _⟩ := h.1
  have hexact := (unitary_model_outer_two_part_bound S n p f h).1
  set q := p ^ f
  have hq1 : 1 ≤ (q : ℤ) := by
    exact_mod_cast Nat.one_le_pow f p hp.pos
  have hprod := prod_pow_sub_neg_one_pow_le hq1 hn
  have hmul : (Nat.card S : ℤ) * (Nat.gcd n (q + 1) : ℤ) ≤
      (q : ℤ) ^ (n ^ 2 - 1) := by
    rw [hexact, ← half_mul_sub_one_add_sum_Icc (by omega : 2 ≤ n), pow_add]
    exact mul_le_mul_of_nonneg_left hprod (pow_nonneg (by omega) _)
  exact_mod_cast hmul

/-- For `StatedClassicalModel S .PSU n p f`,
`Nat.card S * (2 * f * Nat.gcd n (p ^ f + 1)) ≤ 2 * f * (p ^ f) ^ (n ^ 2 - 1)`. -/
theorem card_mul_outer_le_two_mul_pow_psu {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSU n p f) :
    Nat.card S * (2 * f * Nat.gcd n (p ^ f + 1)) ≤ 2 * f * (p ^ f) ^ (n ^ 2 - 1) := by
  calc Nat.card S * (2 * f * Nat.gcd n (p ^ f + 1))
      = 2 * f * (Nat.card S * Nat.gcd n (p ^ f + 1)) := by ring
    _ ≤ 2 * f * (p ^ f) ^ (n ^ 2 - 1) :=
        Nat.mul_le_mul_left (2 * f) (card_mul_gcd_le_pow_psu h)

end ProductBound

section BoundInequalities

/-- For `4 ≤ n` and `1 ≤ f`, `f * n ^ 2 ≤ (f * (n - 2) + 2) ^ 2`. -/
theorem psu_exp_le_of_four_le {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) :
    f * n ^ 2 ≤ (f * (n - 2) + 2) ^ 2 := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 4 := ⟨n - 4, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, f = e + 1 := ⟨f - 1, by omega⟩
  have hsub : d + 4 - 2 = d + 2 := rfl
  rw [hsub]
  have hid : ((e + 1) * (d + 2) + 2) ^ 2 =
      (e + 1) * (d + 4) ^ 2 +
        (d ^ 2 * e ^ 2 + d ^ 2 * e + 4 * d * e ^ 2 + 4 * d * e + 4 * e ^ 2) := by ring
  rw [hid]
  exact Nat.le_add_right _ _

/-- For `4 ≤ n` and `1 ≤ f`, `2 * f * (2 ^ f) ^ (n ^ 2 - 1) ≤ bound (2 * 2 * (2 ^ f) ^ (n - 2))`. -/
theorem two_mul_pow_le_bound_psu_two_of_four_le {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) :
    2 * f * (2 ^ f) ^ (n ^ 2 - 1) ≤ bound (2 * 2 * (2 ^ f) ^ (n - 2)) := by
  set a := f * (n - 2) + 2
  have hm : 2 * 2 * (2 ^ f) ^ (n - 2) = 2 ^ a := by
    rw [← pow_mul, show 2 * 2 * 2 ^ (f * (n - 2)) = 2 ^ (f * (n - 2) + 2) by ring]
  have h1 : 1 ≤ n ^ 2 := by nlinarith
  have hbase : 2 * f * (2 ^ f) ^ (n ^ 2 - 1) ≤ 2 ^ (f * n ^ 2) := by
    calc 2 * f * (2 ^ f) ^ (n ^ 2 - 1)
        ≤ 2 ^ f * (2 ^ f) ^ (n ^ 2 - 1) :=
          Nat.mul_le_mul_right _ (two_mul_le_pow_of_two_le le_rfl hf)
      _ = (2 ^ f) ^ (n ^ 2 - 1 + 1) := (pow_succ' (2 ^ f) _).symm
      _ = (2 ^ f) ^ (n ^ 2) := by rw [Nat.sub_add_cancel h1]
      _ = 2 ^ (f * n ^ 2) := (pow_mul 2 f (n ^ 2)).symm
  have hlog : Nat.log 2 (2 ^ a) = a := Nat.log_pow (by norm_num : 1 < 2) a
  rw [hm]
  calc 2 * f * (2 ^ f) ^ (n ^ 2 - 1)
      ≤ 2 ^ (f * n ^ 2) := hbase
    _ ≤ 2 ^ (a ^ 2) := Nat.pow_le_pow_right (by norm_num) (psu_exp_le_of_four_le hn hf)
    _ = (2 ^ a) ^ a := by rw [sq, pow_mul]
    _ = (2 ^ a) ^ Nat.log 2 (2 ^ a) := by rw [hlog]
    _ ≤ bound (2 ^ a) := pow_log_le_bound (Nat.pow_pos (by norm_num))

/-- For `3 ≤ a`, `2 ^ (a + 2) ≤ 2 * 3 ^ a`. -/
theorem two_pow_add_two_le_two_mul_three_pow {a : ℕ} (ha : 3 ≤ a) :
    2 ^ (a + 2) ≤ 2 * 3 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ k _ ih =>
    calc 2 ^ (k + 1 + 2) = 2 * 2 ^ (k + 2) := by rw [pow_succ']
      _ ≤ 3 * (2 * 3 ^ k) := Nat.mul_le_mul (by norm_num) ih
      _ = 2 * 3 ^ (k + 1) := by rw [pow_succ']; ring

/-- For `4 ≤ n`, `3 ≤ p`, and `1 ≤ f`,
`2 * f * (p ^ f) ^ (n ^ 2 - 1) ≤ bound (2 * p * (p ^ f) ^ (n - 2))`. -/
theorem two_mul_pow_le_bound_psu_odd_of_four_le {n p f : ℕ} (hn : 4 ≤ n) (hp : 3 ≤ p)
    (hf : 1 ≤ f) :
    2 * f * (p ^ f) ^ (n ^ 2 - 1) ≤ bound (2 * p * (p ^ f) ^ (n - 2)) := by
  set a := f * (n - 2) + 1
  have hm : 2 * p * (p ^ f) ^ (n - 2) = 2 * p ^ a := by
    rw [← pow_mul, mul_assoc, ← pow_succ']
  have ha3 : 3 ≤ a := by
    have : 2 ≤ n - 2 := by omega
    have : 2 ≤ f * (n - 2) := le_trans (by omega) (Nat.mul_le_mul hf this)
    omega
  have hlog : a + 2 ≤ Nat.log 2 (2 * p ^ a) := by
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    exact (two_pow_add_two_le_two_mul_three_pow ha3).trans
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hp a))
  have h2f : 2 * f ≤ 2 ^ (a + 2) := by
    have hfa : f ≤ a + 2 := by
      have : f * 1 ≤ f * (n - 2) := Nat.mul_le_mul_left f (by omega)
      omega
    exact (two_mul_le_pow_of_two_le le_rfl hf).trans (Nat.pow_le_pow_right (by norm_num) hfa)
  have hexp : f * (n ^ 2 - 1) ≤ a * (a + 2) := by
    have hsq := psu_exp_le_of_four_le hn hf
    have ha1 : (a + 1) ^ 2 = a * (a + 2) + 1 := by ring
    have hfn : f * (n ^ 2 - 1) + 1 ≤ f * n ^ 2 := by
      obtain ⟨d, rfl⟩ : ∃ d, n = d + 4 := ⟨n - 4, by omega⟩
      obtain ⟨e, rfl⟩ : ∃ e, f = e + 1 := ⟨f - 1, by omega⟩
      have hsub : (d + 4) ^ 2 - 1 = d ^ 2 + 8 * d + 15 := by
        zify [show 1 ≤ (d + 4) ^ 2 by nlinarith]
        ring
      rw [hsub]
      linarith
    have hsq' : (a + 1) ^ 2 = (f * (n - 2) + 2) ^ 2 := rfl
    omega
  have hp0 : 0 < p := by omega
  have h2pa0 : 0 < 2 * p ^ a := Nat.mul_pos (by norm_num) (Nat.pow_pos hp0)
  rw [hm, ← pow_mul]
  calc 2 * f * p ^ (f * (n ^ 2 - 1))
      ≤ 2 ^ (a + 2) * p ^ (a * (a + 2)) :=
        Nat.mul_le_mul h2f (Nat.pow_le_pow_right hp0 hexp)
    _ = (2 * p ^ a) ^ (a + 2) := by rw [mul_pow, pow_mul]
    _ ≤ (2 * p ^ a) ^ Nat.log 2 (2 * p ^ a) := Nat.pow_le_pow_right h2pa0 hlog
    _ ≤ bound (2 * p ^ a) := pow_log_le_bound h2pa0

/-- For `n = 3`, `p = 2`, and `2 ≤ f`,
`2 * f * (2 ^ f) ^ 8 ≤ bound (2 * 2 * 2 ^ f)`. -/
theorem two_mul_pow_le_bound_psu_three_two {f : ℕ} (hf : 2 ≤ f) :
    2 * f * (2 ^ f) ^ 8 ≤ bound (2 * 2 * 2 ^ f) := by
  by_cases hf2 : f = 2
  · subst hf2; decide
  by_cases hf3 : f = 3
  · subst hf3; decide
  have hf4 : 4 ≤ f := by omega
  have hm : 2 * 2 * 2 ^ f = 2 ^ (f + 2) := by ring
  have hlog : Nat.log 2 (2 ^ (f + 2)) = f + 2 := Nat.log_pow (by norm_num : 1 < 2) (f + 2)
  have hexp : 9 * f ≤ (f + 2) ^ 2 := by
    obtain ⟨e, rfl⟩ : ∃ e, f = e + 4 := ⟨f - 4, by omega⟩
    have hid : (e + 4 + 2) ^ 2 = 9 * (e + 4) + (e ^ 2 + 3 * e) := by ring
    rw [hid]
    exact Nat.le_add_right _ _
  rw [hm]
  calc 2 * f * (2 ^ f) ^ 8
      ≤ 2 ^ f * (2 ^ f) ^ 8 := Nat.mul_le_mul_right _ (two_mul_le_pow_of_two_le le_rfl (by omega))
    _ = 2 ^ (9 * f) := by rw [← pow_mul, ← pow_add]; ring_nf
    _ ≤ 2 ^ ((f + 2) ^ 2) := Nat.pow_le_pow_right (by norm_num) hexp
    _ = (2 ^ (f + 2)) ^ (f + 2) := by rw [sq, pow_mul]
    _ = (2 ^ (f + 2)) ^ Nat.log 2 (2 ^ (f + 2)) := by rw [hlog]
    _ ≤ bound (2 ^ (f + 2)) := pow_log_le_bound (Nat.pow_pos (by norm_num))

/-- For `1 ≤ f`, `2 ^ (2 * f + 3) ≤ 2 * 5 ^ (f + 1)`. -/
theorem two_pow_two_mul_add_three_le_two_mul_five_pow {f : ℕ} (hf : 1 ≤ f) :
    2 ^ (2 * f + 3) ≤ 2 * 5 ^ (f + 1) := by
  induction f, hf using Nat.le_induction with
  | base => decide
  | succ k _ ih =>
    have hstep : 2 * (k + 1) + 3 = (2 * k + 3) + 2 := by omega
    rw [hstep, pow_add]
    calc 2 ^ (2 * k + 3) * 2 ^ 2
        ≤ (2 * 5 ^ (k + 1)) * 5 := Nat.mul_le_mul ih (by decide)
      _ = 2 * 5 ^ (k + 1 + 1) := by rw [pow_succ]; ring

/-- For `5 ≤ p` and `1 ≤ f`, `2 * f * (p ^ f) ^ 8 ≤ bound (2 * p * p ^ f)`. -/
theorem two_mul_pow_le_bound_psu_three_five_le {p f : ℕ} (hp : 5 ≤ p) (hf : 1 ≤ f) :
    2 * f * (p ^ f) ^ 8 ≤ bound (2 * p * p ^ f) := by
  have hm : 2 * p * p ^ f = 2 * p ^ (f + 1) := by rw [mul_assoc, ← pow_succ']
  have hlog : 2 * f + 3 ≤ Nat.log 2 (2 * p ^ (f + 1)) := by
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    exact (two_pow_two_mul_add_three_le_two_mul_five_pow hf).trans
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hp (f + 1)))
  have h2f : 2 * f ≤ 2 ^ (2 * f + 3) :=
    (two_mul_le_pow_of_two_le le_rfl hf).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hexp : 8 * f ≤ (f + 1) * (2 * f + 3) := by
    obtain ⟨e, rfl⟩ : ∃ e, f = e + 1 := ⟨f - 1, by omega⟩
    have hid : (e + 1 + 1) * (2 * (e + 1) + 3) = 8 * (e + 1) + (2 * e ^ 2 + e + 2) := by ring
    rw [hid]
    exact Nat.le_add_right _ _
  have hp0 : 0 < p := by omega
  have h2pa0 : 0 < 2 * p ^ (f + 1) := Nat.mul_pos (by norm_num) (Nat.pow_pos hp0)
  rw [hm, ← pow_mul]
  calc 2 * f * p ^ (f * 8)
      = 2 * f * p ^ (8 * f) := by rw [mul_comm f 8]
    _ ≤ 2 ^ (2 * f + 3) * p ^ ((f + 1) * (2 * f + 3)) :=
        Nat.mul_le_mul h2f (Nat.pow_le_pow_right hp0 hexp)
    _ = (2 * p ^ (f + 1)) ^ (2 * f + 3) := by rw [mul_pow, pow_mul]
    _ ≤ (2 * p ^ (f + 1)) ^ Nat.log 2 (2 * p ^ (f + 1)) := Nat.pow_le_pow_right h2pa0 hlog
    _ ≤ bound (2 * p ^ (f + 1)) := pow_log_le_bound h2pa0

/-- For `3 ≤ f`, `2 ^ (f + 4) ≤ 2 * 3 ^ (f + 1)`. -/
theorem two_pow_add_four_le_two_mul_three_pow_succ {f : ℕ} (hf : 3 ≤ f) :
    2 ^ (f + 4) ≤ 2 * 3 ^ (f + 1) := by
  induction f, hf using Nat.le_induction with
  | base => decide
  | succ k _ ih =>
    calc 2 ^ (k + 1 + 4) = 2 * 2 ^ (k + 4) := by rw [pow_succ']
      _ ≤ 3 * (2 * 3 ^ (k + 1)) := Nat.mul_le_mul (by norm_num) ih
      _ = 2 * 3 ^ (k + 1 + 1) := by rw [pow_succ']; ring

/-- For `n = 3`, `p = 3`, and `1 ≤ f`, `2 * f * (3 ^ f) ^ 8 ≤ bound (2 * 3 * 3 ^ f)`. -/
theorem two_mul_pow_le_bound_psu_three_three {f : ℕ} (hf : 1 ≤ f) :
    2 * f * (3 ^ f) ^ 8 ≤ bound (2 * 3 * 3 ^ f) := by
  by_cases hf1 : f = 1
  · subst hf1; decide
  by_cases hf2 : f = 2
  · subst hf2; decide
  have hf3 : 3 ≤ f := by omega
  have hm : 2 * 3 * 3 ^ f = 2 * 3 ^ (f + 1) := by rw [mul_assoc, ← pow_succ']
  have hlog : f + 4 ≤ Nat.log 2 (2 * 3 ^ (f + 1)) :=
    Nat.le_log_of_pow_le (by norm_num) (two_pow_add_four_le_two_mul_three_pow_succ hf3)
  have h2f : 2 * f ≤ 2 ^ (f + 4) :=
    (two_mul_le_pow_of_two_le le_rfl hf).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hexp : 8 * f ≤ (f + 1) * (f + 4) := by
    obtain ⟨e, rfl⟩ : ∃ e, f = e + 3 := ⟨f - 3, by omega⟩
    have hid : (e + 3 + 1) * (e + 3 + 4) = 8 * (e + 3) + (e ^ 2 + 3 * e + 4) := by ring
    rw [hid]
    exact Nat.le_add_right _ _
  have h2pa0 : 0 < 2 * 3 ^ (f + 1) := Nat.mul_pos (by norm_num) (Nat.pow_pos (by norm_num))
  rw [hm, ← pow_mul]
  calc 2 * f * 3 ^ (f * 8)
      = 2 * f * 3 ^ (8 * f) := by rw [mul_comm f 8]
    _ ≤ 2 ^ (f + 4) * 3 ^ ((f + 1) * (f + 4)) :=
        Nat.mul_le_mul h2f (Nat.pow_le_pow_right (by norm_num) hexp)
    _ = (2 * 3 ^ (f + 1)) ^ (f + 4) := by rw [mul_pow, pow_mul]
    _ ≤ (2 * 3 ^ (f + 1)) ^ Nat.log 2 (2 * 3 ^ (f + 1)) := Nat.pow_le_pow_right h2pa0 hlog
    _ ≤ bound (2 * 3 ^ (f + 1)) := pow_log_le_bound h2pa0

/-- Maróti's numerical bound for `PSU(n, p ^ f)` (`n ≥ 3`, `(n, p ^ f) ≠ (3, 2)`):
`Nat.card S * (2 * f * Nat.gcd n (p ^ f + 1)) ≤ bound (2 * p * (p ^ f) ^ (n - 2))`. -/
theorem card_mul_outer_le_bound_psu {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSU n p f) :
    Nat.card S * (2 * f * Nat.gcd n (p ^ f + 1)) ≤ bound (2 * p * (p ^ f) ^ (n - 2)) := by
  obtain ⟨hp, hf, hn, h32⟩ := h.1
  refine (card_mul_outer_le_two_mul_pow_psu h).trans ?_
  by_cases hn4 : 4 ≤ n
  · by_cases hp2 : p = 2
    · subst hp2
      exact two_mul_pow_le_bound_psu_two_of_four_le hn4 hf
    · have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      exact two_mul_pow_le_bound_psu_odd_of_four_le hn4 hp3 hf
  · have hn3 : n = 3 := by omega
    subst hn3
    change 2 * f * (p ^ f) ^ 8 ≤ bound (2 * p * (p ^ f) ^ 1)
    rw [pow_one]
    by_cases hp2 : p = 2
    · subst hp2
      have hf2 : 2 ≤ f := by
        by_contra hlt
        have hf1 : f = 1 := by omega
        exact h32 (by rw [hf1, pow_one])
      exact two_mul_pow_le_bound_psu_three_two hf2
    · by_cases hp3 : p = 3
      · subst hp3
        exact two_mul_pow_le_bound_psu_three_three hf
      · have hp5 : 5 ≤ p := by
          have hp2le := hp.two_le
          have hp4 : p ≠ 4 := fun h4 => by subst h4; exact absurd hp (by decide)
          omega
        exact two_mul_pow_le_bound_psu_three_five_le hp5 hf

end BoundInequalities

end Maroti
