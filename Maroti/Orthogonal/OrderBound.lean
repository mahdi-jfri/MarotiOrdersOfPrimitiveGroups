module

public import Maroti.Classical.AutBound
public import Maroti.Orthogonal.Heisenberg
public import CFSG.ClassicalInvolution.Orders.Orthogonal
public import CFSG.Timmesfeld.Orders.ClassicalOmega

/-!
# Order Bounds and Maróti's Inequality for Orthogonal Groups

This file proves explicit upper bounds on `Nat.card S * c` (where `c` is the outer automorphism
divisibility bound from `Maroti/Classical/AutBound.lean`) for the three orthogonal families
`PΩ(2n + 1, p^f)`, `PΩ⁺(2n, p^f)`, and `PΩ⁻(2n, p^f)`, using the group order formulas from
`CFSG/ClassicalInvolution/Orders/Orthogonal.lean` and `CFSG/Timmesfeld/Orders/ClassicalOmega.lean`,
and compares them with `Maroti.bound (p * (p ^ f) ^ (dim V - 4))` (Maróti, Section 2, Step 2,
page 634).

For `PΩ(2n + 1, p^f)` (`n ≥ 3`, `p` odd), `Nat.card S * (2 * f) ≤ bound (p * (p ^ f) ^ (2 * n - 3))`
holds for all parameters (`Maroti.card_mul_outer_le_bound_pOmegaOdd`), which combines with
`Maroti.index_ge_of_statedClassicalModel_pOmegaOdd` and `Maroti.card_outerAut_pOmegaOdd_dvd` to
prove `Maroti.orthogonalOddCase`.

For `PΩ⁺(2n, p^f)` and `PΩ⁻(2n, p^f)` (`n ≥ 4`),
`Nat.card S * c ≤ bound (p * (p ^ f) ^ (2 * n - 4))` holds whenever
`¬(n = 4 ∧ p = 2 ∧ f = 1)` (`Maroti.card_mul_outer_le_bound_pOmegaPlus` and
`Maroti.card_mul_outer_le_bound_pOmegaMinus`).
-/

@[expose] public section

namespace Maroti

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution
  CFSG.Timmesfeld.ClassicalOrders CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open Finset

section ProdBounds

theorem prod_pow_two_mul_sub_one_le_mul {q m : ℕ} (hm : 1 ≤ m) :
    ∏ i ∈ Icc 1 m, (q ^ (2 * i) - 1) ≤ (q ^ 2 - 1) * q ^ (m * (m + 1) - 2) := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hk2 : 2 ≤ k * (k + 1) := by nlinarith
    rw [Finset.prod_Icc_succ_top (by omega)]
    calc (∏ i ∈ Icc 1 k, (q ^ (2 * i) - 1)) * (q ^ (2 * (k + 1)) - 1)
        ≤ ((q ^ 2 - 1) * q ^ (k * (k + 1) - 2)) * q ^ (2 * (k + 1)) :=
          Nat.mul_le_mul ih (Nat.sub_le _ _)
      _ = (q ^ 2 - 1) * q ^ (k * (k + 1) - 2 + 2 * (k + 1)) := by rw [mul_assoc, ← pow_add]
      _ = (q ^ 2 - 1) * q ^ ((k + 1) * (k + 1 + 1) - 2) := by
          congr 2
          have : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by ring
          omega

theorem pow_add_one_mul_pow_two_sub_one_le {q n : ℕ} (hq : 1 ≤ q) (hn : 2 ≤ n) :
    (q ^ n + 1) * (q ^ 2 - 1) ≤ q ^ (n + 2) := by
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q hq
  have hqn : q ^ 2 ≤ q ^ n := Nat.pow_le_pow_right hq hn
  calc (q ^ n + 1) * (q ^ 2 - 1)
      = q ^ n * (q ^ 2 - 1) + (q ^ 2 - 1) := by ring
    _ ≤ q ^ n * (q ^ 2 - 1) + q ^ n := Nat.add_le_add_left ( (Nat.sub_le _ _).trans hqn ) _
    _ = q ^ n * (q ^ 2 - 1 + 1) := by ring
    _ = q ^ (n + 2) := by rw [Nat.sub_add_cancel hq2, ← pow_add]

theorem mul_prod_pow_two_mul_sub_one_le {q n : ℕ} (hq : 1 ≤ q) (hn : 2 ≤ n) :
    (q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) ≤ q ^ (n * n) := by
  have hm : 1 ≤ n - 1 := by omega
  have hsub : 2 ≤ (n - 1) * n := by
    obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
    nlinarith
  have h1 := prod_pow_two_mul_sub_one_le_mul (q := q) hm
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h1
  calc (q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)
      ≤ (q ^ n + 1) * ((q ^ 2 - 1) * q ^ ((n - 1) * n - 2)) := Nat.mul_le_mul_left _ h1
    _ = ((q ^ n + 1) * (q ^ 2 - 1)) * q ^ ((n - 1) * n - 2) := by ring
    _ ≤ q ^ (n + 2) * q ^ ((n - 1) * n - 2) :=
        Nat.mul_le_mul_right _ (pow_add_one_mul_pow_two_sub_one_le hq hn)
    _ = q ^ (n + 2 + ((n - 1) * n - 2)) := (pow_add q _ _).symm
    _ = q ^ (n * n) := by
        congr 1
        obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
        have h1 : d + 2 - 1 = d + 1 := rfl
        rw [h1]
        have : (d + 1) * (d + 2) = d * d + 3 * d + 2 := by ring
        have : (d + 2) * (d + 2) = d * d + 4 * d + 4 := by ring
        omega

end ProdBounds

section CardBounds

/-- For `PΩ(2n + 1, p^f)`, `Nat.card S * (2 * f) ≤ (p ^ f) ^ (n * (2 * n + 1) + 1)`. -/
theorem card_mul_outer_le_pow_pOmegaOdd {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .POmegaOdd n p f) :
    Nat.card S * (2 * f) ≤ (p ^ f) ^ (n * (2 * n + 1) + 1) := by
  obtain ⟨⟨hp, hf, hn, hp2⟩, K, _, _, hK, ⟨e⟩⟩ := h
  set q := p ^ f
  have hq1 : 1 ≤ q := Nat.one_le_pow f p hp.pos
  have hodd : Odd q := (hp.odd_of_ne_two hp2).pow
  have hcard : Nat.card S = ordBC n q := by
    rw [Nat.card_congr e.toEquiv]
    exact card_statedProj_statedOmega_quadOdd_eq_ordBC hp hp2 hK hn
  have hgcd : Nat.gcd 2 (q - 1) = 2 := gcd_two_sub_one_of_odd hodd
  have hS2 : Nat.card S * 2 ≤ q ^ (n * (2 * n + 1)) := by
    rw [hcard, ordBC, hgcd]
    calc q ^ (n * n) * (∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1)) / 2 * 2
        ≤ q ^ (n * n) * ∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1) := Nat.div_mul_le_self _ 2
      _ ≤ q ^ (n * n) * q ^ (n * (n + 1)) :=
          Nat.mul_le_mul_left _ (prod_pow_two_mul_sub_one_le q n)
      _ = q ^ (n * n + n * (n + 1)) := (pow_add q _ _).symm
      _ = q ^ (n * (2 * n + 1)) := by congr 1; ring
  have hf_le : f ≤ q := by
    have := two_mul_le_pow_of_two_le hp.two_le hf
    omega
  calc Nat.card S * (2 * f)
      = (Nat.card S * 2) * f := by ring
    _ ≤ q ^ (n * (2 * n + 1)) * q := Nat.mul_le_mul hS2 hf_le
    _ = q ^ (n * (2 * n + 1) + 1) := (pow_succ q _).symm

/-- For `PΩ⁺(2n, p^f)`,
`Nat.card S * (gcd(4, q^n - 1) * f * (if n = 4 then 6 else 2)) ≤ 3 * q ^ (n * (2 * n - 1) + 1)`. -/
theorem card_mul_outer_le_pow_pOmegaPlus {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .POmegaPlus n p f) :
    Nat.card S * (Nat.gcd 4 ((p ^ f) ^ n - 1) * f * (if n = 4 then 6 else 2)) ≤
      3 * (p ^ f) ^ (n * (2 * n - 1) + 1) := by
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := h
  set q := p ^ f
  have hq1 : 1 ≤ q := Nat.one_le_pow f p hp.pos
  have hqn1 : 1 ≤ q ^ n := Nat.one_le_pow n q hq1
  have hprod_le : q ^ (n * (n - 1)) * (q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) ≤
      q ^ (n * (2 * n - 1)) := by
    calc q ^ (n * (n - 1)) * (q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)
        ≤ q ^ (n * (n - 1)) * q ^ n * q ^ ((n - 1) * (n - 1 + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
            (prod_pow_two_mul_sub_one_le q (n - 1))
      _ = q ^ (n * (n - 1) + n + (n - 1) * (n - 1 + 1)) := by rw [← pow_add, ← pow_add]
      _ = q ^ (n * (2 * n - 1)) := by
          congr 1
          obtain ⟨d, rfl⟩ : ∃ d, n = d + 4 := ⟨n - 4, by omega⟩
          have h1 : d + 4 - 1 = d + 3 := rfl
          have h2 : 2 * (d + 4) - 1 = 2 * d + 7 := rfl
          rw [h1, h2]
          ring
  have hSd : Nat.card S * Nat.gcd 4 (q ^ n - 1) ≤ q ^ (n * (2 * n - 1)) := by
    by_cases hp2 : p = 2
    · have : CharP K 2 := Maroti.charP_of_card_eq Nat.prime_two hf (hp2 ▸ hK)
      have hZ := card_statedProj_statedOmega_quadPlus (K := K) hn
      rw [hK] at hZ
      have hcard : Nat.card S =
          q ^ (n * (n - 1)) * (q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) := by
        rw [Nat.card_congr e.toEquiv]
        apply Nat.cast_injective (R := ℤ)
        rw [hZ]
        push_cast [Nat.cast_sub hqn1, cast_prod_pow_sub_one' hq1]
        rfl
      have hodd : Odd (q ^ n - 1) := by
        have heven : Even (q ^ n) := by
          rw [show q = 2 ^ f from hp2 ▸ rfl, ← pow_mul]
          exact Nat.even_pow.mpr ⟨even_two, Nat.mul_ne_zero (by omega) (by omega)⟩
        exact Nat.Even.sub_odd hqn1 heven odd_one
      have hgcd : Nat.gcd 4 (q ^ n - 1) = 1 := by
        have h2c : Nat.Coprime 2 (q ^ n - 1) := Nat.coprime_two_left.mpr hodd
        simpa using h2c.pow_left 2
      rw [hgcd, mul_one, hcard]
      exact hprod_le
    · have hcard : Nat.card S = ordD n q := by
        rw [Nat.card_congr e.toEquiv]
        exact card_statedProj_statedOmega_quadPlus_eq_ordD hp hp2 hK hn
      rw [hcard, ordD]
      exact (Nat.div_mul_le_self _ _).trans hprod_le
  have hk : (if n = 4 then 6 else 2) ≤ 6 := by split_ifs <;> norm_num
  have h2f : 2 * f ≤ q := two_mul_le_pow_of_two_le hp.two_le hf
  calc Nat.card S * (Nat.gcd 4 (q ^ n - 1) * f * (if n = 4 then 6 else 2))
      = (Nat.card S * Nat.gcd 4 (q ^ n - 1)) * (f * (if n = 4 then 6 else 2)) := by ring
    _ ≤ q ^ (n * (2 * n - 1)) * (f * 6) :=
        Nat.mul_le_mul hSd (Nat.mul_le_mul_left f hk)
    _ = 3 * (q ^ (n * (2 * n - 1)) * (2 * f)) := by ring
    _ ≤ 3 * (q ^ (n * (2 * n - 1)) * q) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left _ h2f)
    _ = 3 * q ^ (n * (2 * n - 1) + 1) := by rw [← pow_succ]

/-- For `PΩ⁻(2n, p^f)`,
`Nat.card S * (gcd(4, q^n + 1) * f * 2) ≤ 3 * q ^ (n * (2 * n - 1) + 1)`. -/
theorem card_mul_outer_le_pow_pOmegaMinus {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .POmegaMinus n p f) :
    Nat.card S * (Nat.gcd 4 ((p ^ f) ^ n + 1) * f * 2) ≤
      3 * (p ^ f) ^ (n * (2 * n - 1) + 1) := by
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h
  set q := p ^ f
  have hq1 : 1 ≤ q := Nat.one_le_pow f p hp.pos
  have hprod_le : q ^ (n * (n - 1)) * (q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) ≤
      q ^ (n * (2 * n - 1)) := by
    calc q ^ (n * (n - 1)) * (q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)
        = q ^ (n * (n - 1)) * ((q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by ring
      _ ≤ q ^ (n * (n - 1)) * q ^ (n * n) :=
          Nat.mul_le_mul_left _ (mul_prod_pow_two_mul_sub_one_le hq1 (by omega))
      _ = q ^ (n * (n - 1) + n * n) := (pow_add q _ _).symm
      _ = q ^ (n * (2 * n - 1)) := by
          congr 1
          obtain ⟨d, rfl⟩ : ∃ d, n = d + 4 := ⟨n - 4, by omega⟩
          have h1 : d + 4 - 1 = d + 3 := rfl
          have h2 : 2 * (d + 4) - 1 = 2 * d + 7 := rfl
          rw [h1, h2]
          ring
  have hSd : Nat.card S * Nat.gcd 4 (q ^ n + 1) ≤ q ^ (n * (2 * n - 1)) := by
    by_cases hp2 : p = 2
    · have : CharP K 2 := Maroti.charP_of_card_eq Nat.prime_two hf (hp2 ▸ hK)
      have hZ := card_statedProj_statedOmega_quadMinus (K := K) hn hirr
      rw [hK] at hZ
      have hcard : Nat.card S =
          q ^ (n * (n - 1)) * (q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) := by
        rw [Nat.card_congr e.toEquiv]
        apply Nat.cast_injective (R := ℤ)
        rw [hZ]
        push_cast [cast_prod_pow_sub_one' hq1]
        rfl
      have hodd : Odd (q ^ n + 1) := by
        have heven : Even (q ^ n) := by
          rw [show q = 2 ^ f from hp2 ▸ rfl, ← pow_mul]
          exact Nat.even_pow.mpr ⟨even_two, Nat.mul_ne_zero (by omega) (by omega)⟩
        exact heven.add_odd odd_one
      have hgcd : Nat.gcd 4 (q ^ n + 1) = 1 := by
        have h2c : Nat.Coprime 2 (q ^ n + 1) := Nat.coprime_two_left.mpr hodd
        simpa using h2c.pow_left 2
      rw [hgcd, mul_one, hcard]
      exact hprod_le
    · have hcard : Nat.card S = ordTwistedD n q := by
        rw [Nat.card_congr e.toEquiv]
        exact card_statedProj_statedOmega_quadMinus_eq_ordTwistedD hp hp2 hK hn hirr
      rw [hcard, ordTwistedD]
      exact (Nat.div_mul_le_self _ _).trans hprod_le
  have h2f : 2 * f ≤ q := two_mul_le_pow_of_two_le hp.two_le hf
  calc Nat.card S * (Nat.gcd 4 (q ^ n + 1) * f * 2)
      = (Nat.card S * Nat.gcd 4 (q ^ n + 1)) * (2 * f) := by ring
    _ ≤ q ^ (n * (2 * n - 1)) * q := Nat.mul_le_mul hSd h2f
    _ = q ^ (n * (2 * n - 1) + 1) := (pow_succ q _).symm
    _ ≤ 3 * q ^ (n * (2 * n - 1) + 1) := Nat.le_mul_of_pos_left _ (by norm_num)

end CardBounds

section BoundInequalities

theorem le_log_of_two_le {p a : ℕ} (hp : 2 ≤ p) : a ≤ Nat.log 2 (p ^ a) :=
  Nat.le_log_of_pow_le (by norm_num) (Nat.pow_le_pow_left hp a)

theorem odd_exp_le {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f) :
    f * (n * (2 * n + 1) + 1) ≤ (f * (2 * n - 3) + 1) * (f * (2 * n - 3) + 1 + 2) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 3 := ⟨n - 3, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, f = e + 1 := ⟨f - 1, by omega⟩
  have hsub : 2 * (d + 3) - 3 = 2 * d + 3 := by omega
  rw [hsub]
  have hid : ((e + 1) * (2 * d + 3) + 1) * ((e + 1) * (2 * d + 3) + 1 + 2) =
      (e + 1) * ((d + 3) * (2 * (d + 3) + 1) + 1) +
        (4 * d ^ 2 * e ^ 2 + 6 * d ^ 2 * e + 2 * d ^ 2 + 12 * d * e ^ 2 + 19 * d * e + 7 * d +
          9 * e ^ 2 + 8 * e + 2) := by ring
  rw [hid]
  exact Nat.le_add_right _ _

theorem even_exp_le_of_five_le {n f : ℕ} (hn : 5 ≤ n) (hf : 1 ≤ f) :
    f * (n * (2 * n - 1) + 1) + 2 ≤ (f * (2 * n - 4) + 1) * (f * (2 * n - 4) + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 5 := ⟨n - 5, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, f = e + 1 := ⟨f - 1, by omega⟩
  have h1 : 2 * (d + 5) - 1 = 2 * d + 9 := by omega
  have h2 : 2 * (d + 5) - 4 = 2 * d + 6 := by omega
  rw [h1, h2]
  have hid : ((e + 1) * (2 * d + 6) + 1) * ((e + 1) * (2 * d + 6) + 1) =
      ((e + 1) * ((d + 5) * (2 * d + 9) + 1) + 2) +
        (4 * d ^ 2 * e ^ 2 + 6 * d ^ 2 * e + 2 * d ^ 2 + 24 * d * e ^ 2 + 33 * d * e + 9 * d +
          36 * e ^ 2 + 38 * e + 1) := by ring
  rw [hid]
  exact Nat.le_add_right _ _

theorem even_exp_le_of_two_le_f {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f) :
    f * (n * (2 * n - 1) + 1) + 2 ≤ (f * (2 * n - 4) + 1) * (f * (2 * n - 4) + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 4 := ⟨n - 4, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, f = e + 2 := ⟨f - 2, by omega⟩
  have h1 : 2 * (d + 4) - 1 = 2 * d + 7 := by omega
  have h2 : 2 * (d + 4) - 4 = 2 * d + 4 := by omega
  rw [h1, h2]
  have hid : ((e + 2) * (2 * d + 4) + 1) * ((e + 2) * (2 * d + 4) + 1) =
      ((e + 2) * ((d + 4) * (2 * d + 7) + 1) + 2) +
        (4 * d ^ 2 * e ^ 2 + 14 * d ^ 2 * e + 12 * d ^ 2 + 16 * d * e ^ 2 + 53 * d * e + 42 * d +
          16 * e ^ 2 + 43 * e + 21) := by ring
  rw [hid]
  exact Nat.le_add_right _ _

/-- For `n ≥ 3`, `p ≥ 3`, `f ≥ 1`,
`(p ^ f) ^ (n * (2 * n + 1) + 1) ≤ bound (p * (p ^ f) ^ (2 * n - 3))`. -/
theorem pow_le_bound_pOmegaOdd {n p f : ℕ} (hn : 3 ≤ n) (hp : 3 ≤ p) (hf : 1 ≤ f) :
    (p ^ f) ^ (n * (2 * n + 1) + 1) ≤ bound (p * (p ^ f) ^ (2 * n - 3)) := by
  set a := f * (2 * n - 3) + 1
  have hm : p * (p ^ f) ^ (2 * n - 3) = p ^ a := by
    rw [← pow_mul, ← pow_succ']
  have ha4 : 4 ≤ a := by
    have : 3 ≤ 2 * n - 3 := by omega
    have : 3 ≤ f * (2 * n - 3) := le_trans (by omega) (Nat.mul_le_mul hf this)
    omega
  have hp0 : 0 < p := by omega
  have hpa0 : 0 < p ^ a := Nat.pow_pos hp0
  rw [hm, ← pow_mul]
  calc p ^ (f * (n * (2 * n + 1) + 1))
      ≤ p ^ (a * (a + 2)) := Nat.pow_le_pow_right hp0 (odd_exp_le hn hf)
    _ ≤ p ^ (a * Nat.log 2 (p ^ a)) :=
        Nat.pow_le_pow_right hp0 (Nat.mul_le_mul_left a (add_two_le_log_of_three_le hp ha4))
    _ = (p ^ a) ^ Nat.log 2 (p ^ a) := by rw [pow_mul]
    _ ≤ bound (p ^ a) := pow_log_le_bound hpa0

/-- For `n ≥ 4`, `p ≥ 2`, `f ≥ 1` with `¬(n = 4 ∧ p = 2 ∧ f = 1)`,
`3 * (p ^ f) ^ (n * (2 * n - 1) + 1) ≤ bound (p * (p ^ f) ^ (2 * n - 4))`. -/
theorem three_mul_pow_le_bound_pOmegaEven {n p f : ℕ} (hn : 4 ≤ n) (hp : 2 ≤ p) (hf : 1 ≤ f)
    (hnot : ¬(n = 4 ∧ p = 2 ∧ f = 1)) :
    3 * (p ^ f) ^ (n * (2 * n - 1) + 1) ≤ bound (p * (p ^ f) ^ (2 * n - 4)) := by
  set a := f * (2 * n - 4) + 1
  have hm : p * (p ^ f) ^ (2 * n - 4) = p ^ a := by
    rw [← pow_mul, ← pow_succ']
  have hp0 : 0 < p := by omega
  have hpa0 : 0 < p ^ a := Nat.pow_pos hp0
  have h3p2 : 3 ≤ p ^ 2 := by
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp 2
  have hbase : 3 * (p ^ f) ^ (n * (2 * n - 1) + 1) ≤ p ^ (f * (n * (2 * n - 1) + 1) + 2) := by
    rw [← pow_mul]
    calc 3 * p ^ (f * (n * (2 * n - 1) + 1))
        ≤ p ^ 2 * p ^ (f * (n * (2 * n - 1) + 1)) := Nat.mul_le_mul_right _ h3p2
      _ = p ^ (f * (n * (2 * n - 1) + 1) + 2) := by rw [pow_add, mul_comm]
  rw [hm]
  have hexp : f * (n * (2 * n - 1) + 1) + 2 ≤ a * Nat.log 2 (p ^ a) := by
    by_cases hn5 : 5 ≤ n
    · exact (even_exp_le_of_five_le hn5 hf).trans
        (Nat.mul_le_mul_left a (le_log_of_two_le hp))
    · have hn4 : n = 4 := by omega
      by_cases hf2 : 2 ≤ f
      · exact (even_exp_le_of_two_le_f hn hf2).trans
          (Nat.mul_le_mul_left a (le_log_of_two_le hp))
      · have hf1 : f = 1 := by omega
        have hp3 : 3 ≤ p := by omega
        subst hn4 hf1
        have ha5 : a = 5 := rfl
        have hlog : 7 ≤ Nat.log 2 (p ^ a) := by
          have := add_two_le_log_of_three_le hp3 (a := a) (by omega)
          omega
        calc 1 * (4 * (2 * 4 - 1) + 1) + 2 = 31 := by norm_num
          _ ≤ 5 * 7 := by norm_num
          _ ≤ a * Nat.log 2 (p ^ a) := by rw [ha5]; exact Nat.mul_le_mul_left 5 hlog
  calc 3 * (p ^ f) ^ (n * (2 * n - 1) + 1)
      ≤ p ^ (f * (n * (2 * n - 1) + 1) + 2) := hbase
    _ ≤ p ^ (a * Nat.log 2 (p ^ a)) := Nat.pow_le_pow_right hp0 hexp
    _ = (p ^ a) ^ Nat.log 2 (p ^ a) := by rw [pow_mul]
    _ ≤ bound (p ^ a) := pow_log_le_bound hpa0

/-- Maróti's numerical bound for `PΩ(2n + 1, p^f)` (`n ≥ 3`, `p` odd). -/
theorem card_mul_outer_le_bound_pOmegaOdd {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .POmegaOdd n p f) :
    Nat.card S * (2 * f) ≤ bound (p * (p ^ f) ^ (2 * n - 3)) := by
  obtain ⟨hp, hf, hn, hp2⟩ := h.1
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  exact (card_mul_outer_le_pow_pOmegaOdd h).trans (pow_le_bound_pOmegaOdd hn hp3 hf)

/-- Maróti's numerical bound for `PΩ⁺(2n, p^f)` (`n ≥ 4`, `(n, p, f) ≠ (4, 2, 1)`). -/
theorem card_mul_outer_le_bound_pOmegaPlus {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .POmegaPlus n p f) (hnot : ¬(n = 4 ∧ p = 2 ∧ f = 1)) :
    Nat.card S * (Nat.gcd 4 ((p ^ f) ^ n - 1) * f * (if n = 4 then 6 else 2)) ≤
      bound (p * (p ^ f) ^ (2 * n - 4)) := by
  obtain ⟨hp, hf, hn⟩ := h.1
  exact (card_mul_outer_le_pow_pOmegaPlus h).trans
    (three_mul_pow_le_bound_pOmegaEven hn hp.two_le hf hnot)

/-- Maróti's numerical bound for `PΩ⁻(2n, p^f)` (`n ≥ 4`, `(n, p, f) ≠ (4, 2, 1)`). -/
theorem card_mul_outer_le_bound_pOmegaMinus {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .POmegaMinus n p f) (hnot : ¬(n = 4 ∧ p = 2 ∧ f = 1)) :
    Nat.card S * (Nat.gcd 4 ((p ^ f) ^ n + 1) * f * 2) ≤
      bound (p * (p ^ f) ^ (2 * n - 4)) := by
  obtain ⟨hp, hf, hn⟩ := h.1
  exact (card_mul_outer_le_pow_pOmegaMinus h).trans
    (three_mul_pow_le_bound_pOmegaEven hn hp.two_le hf hnot)

/-- Theorem 1.1 for almost simple groups with socle `PΩ(2n + 1, p^f)` (`n ≥ 3`, `p` odd). -/
theorem orthogonalOddCase : AlmostSimpleCase (ClassicalSocle .POmegaOdd) := by
  intro α _ G S _ _ hAS ⟨n, p, f, hModel⟩
  right; right
  have hf : 1 ≤ f := hModel.1.2.1
  exact hAS.card_le_bound_of_outerAut_dvd (by omega)
    (fun H hH => index_ge_of_statedClassicalModel_pOmegaOdd hModel hH)
    (card_outerAut_pOmegaOdd_dvd hModel)
    (card_mul_outer_le_bound_pOmegaOdd hModel)

end BoundInequalities

end Maroti
