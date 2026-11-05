module

public import Maroti.AlmostSimple.Basic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalOddOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalPlusOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalMinusOuterOrder

/-!
# Outer Automorphism Bounds for Classical Simple Groups

This file proves explicit upper bounds on `Nat.card (OuterAut S)` for the five non-linear
classical families (`PSU`, `PSp`, `PΩ`, `PΩ⁺`, `PΩ⁻`) defined by
`CFSG.Open.StatedClassicalModel`, and deduces `Maroti.autBound_otherClassical`:
every finite group `S` satisfying `OtherClassicalSocle S` has
`Nat.card (MulAut S) ≤ Nat.card S ^ 2` (Maróti, Section 2, Step 1, page 634).

The outer automorphism bounds come from:
* the unitary outer bound `CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound`
  (`CFSG/LocalAnalysis/ComponentInitial/UnitaryModelOuterTwoPart.lean`),
* the symplectic outer bound
  `CFSG.LocalAnalysis.ComponentInitial.symplectic_model_outer_two_part_bound`
  (`CFSG/LocalAnalysis/ComponentInitial/SymplecticModelOuterTwoPart.lean`),
* the odd-orthogonal outer bound
  `CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter.card_outer_dvd_of_pOmegaOdd`
  (`CFSG/LocalAnalysis/ComponentInitial/OrthogonalOddOuterOrder.lean`),
* the plus-orthogonal outer bound
  `CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter.card_outer_dvd_of_pOmegaPlus`
  (`CFSG/LocalAnalysis/ComponentInitial/OrthogonalPlusOuterOrder.lean`), and
* the minus-orthogonal outer bound
  `CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter.card_outer_dvd_of_pOmegaMinus`
  (`CFSG/LocalAnalysis/ComponentInitial/OrthogonalMinusOuterOrder.lean`).
-/

@[expose] public section

namespace Maroti

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open Finset

/-- For `PSU(n, p^f)`, `|OuterAut S| = 2 * f * Nat.gcd n (p ^ f + 1)`. -/
theorem card_outerAut_psu_eq {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSU n p f) :
    Nat.card (OuterAut S) = 2 * f * Nat.gcd n (p ^ f + 1) :=
  (unitary_model_outer_two_part_bound S n p f h).2.2.1

/-- For `PSp(2n, p^f)`, `|OuterAut S|` divides `2 * f * Nat.gcd 2 (p ^ f - 1)`. -/
theorem card_outerAut_psp_dvd {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSp n p f) :
    Nat.card (OuterAut S) ∣ 2 * f * Nat.gcd 2 (p ^ f - 1) :=
  (symplectic_model_outer_two_part_bound S n p f h).2.1

/-- For `PSp(2n, p^f)` with `n ≥ 3`, `|OuterAut S|` divides `f * Nat.gcd 2 (p ^ f - 1)`. -/
theorem card_outerAut_psp_dvd_of_three_le {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSp n p f) (hn : 3 ≤ n) :
    Nat.card (OuterAut S) ∣ f * Nat.gcd 2 (p ^ f - 1) :=
  (symplectic_model_outer_two_part_bound S n p f h).2.2.2.2 hn

/-- For `PΩ(2n+1, p^f)`, `|OuterAut S|` divides `2 * f`. -/
theorem card_outerAut_pOmegaOdd_dvd {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .POmegaOdd n p f) :
    Nat.card (OuterAut S) ∣ 2 * f :=
  card_outer_dvd_of_pOmegaOdd S h

/-- For `PΩ⁺(2n, p^f)`, `|OuterAut S|` divides
`Nat.gcd 4 ((p ^ f) ^ n - 1) * f * (if n = 4 then 6 else 2)`. -/
theorem card_outerAut_pOmegaPlus_dvd {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .POmegaPlus n p f) :
    Nat.card (OuterAut S) ∣ Nat.gcd 4 ((p ^ f) ^ n - 1) * f * (if n = 4 then 6 else 2) :=
  card_outer_dvd_of_pOmegaPlus S h

/-- For `PΩ⁻(2n, p^f)`, `|OuterAut S|` divides `Nat.gcd 4 ((p ^ f) ^ n + 1) * f * 2`. -/
theorem card_outerAut_pOmegaMinus_dvd {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .POmegaMinus n p f) :
    Nat.card (OuterAut S) ∣ Nat.gcd 4 ((p ^ f) ^ n + 1) * f * 2 :=
  card_outer_dvd_of_pOmegaMinus S h

/-- Lower bound `(p ^ f) ^ 3 ≤ Nat.card S` for any orthogonal model `S`. -/
theorem pow_three_le_card_of_orthogonal {S : Type} [Group S] [Finite S] {t : StatedLieTag}
    {n p f : ℕ} (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (h : StatedClassicalModel S t n p f) :
    21 * (p ^ f) ^ 3 ≤ Nat.card S := by
  have hdvd : (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) ∣ Nat.card S := by
    rcases ht with rfl | rfl | rfl
    · obtain ⟨⟨_, _, hn, -⟩, K, _, _, hK, ⟨φ⟩⟩ := h
      rw [Nat.card_congr φ.toEquiv]
      have h3 := OrthogonalTwoPart.card_SL_three_dvd_tri hn (fun w : Unit → K => w () ^ 2)
      rwa [← OrthogonalTwoPart.statedQuadOdd_eq, OrthogonalTwoPart.card_SL_three, hK] at h3
    · obtain ⟨⟨_, _, hn⟩, K, _, _, hK, ⟨φ⟩⟩ := h
      rw [Nat.card_congr φ.toEquiv]
      have h3 := OrthogonalTwoPart.card_SL_three_dvd_plus (K := K) (by omega : 3 ≤ n)
      rwa [OrthogonalTwoPart.card_SL_three, hK] at h3
    · obtain ⟨⟨_, _, hn⟩, K, _, _, hK, b, c, -, ⟨φ⟩⟩ := h
      rw [Nat.card_congr φ.toEquiv]
      have h3 := OrthogonalTwoPart.card_SL_three_dvd_tri (by omega : 3 ≤ n - 1)
        (fun w : Fin 2 → K => w 0 ^ 2 + b * w 0 * w 1 + c * w 1 ^ 2)
      rwa [← OrthogonalTwoPart.statedQuadMinus_eq, OrthogonalTwoPart.card_SL_three, hK] at h3
  have hp : p.Prime := h.1.1
  have hf : 1 ≤ f := h.1.2.1
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf)
  have hq2_sub : 3 ≤ (p ^ f) ^ 2 - 1 := by
    have : 2 ^ 2 ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq2 2
    omega
  have hq3_sub : 7 ≤ (p ^ f) ^ 3 - 1 := by
    have : 2 ^ 3 ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left hq2 3
    omega
  have h21 : 21 ≤ ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) := by
    calc 21 = 3 * 7 := by norm_num
      _ ≤ ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) := Nat.mul_le_mul hq2_sub hq3_sub
  calc 21 * (p ^ f) ^ 3
      = (p ^ f) ^ 3 * 21 := by ring
    _ ≤ (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) := Nat.mul_le_mul_left _ h21
    _ ≤ Nat.card S := Nat.le_of_dvd Nat.card_pos hdvd

/-- Lower bound `(p ^ f) ^ 4 ≤ Nat.card S` for `PSp(2n, p^f)`. -/
theorem pow_four_le_card_of_psp {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSp n p f) :
    (p ^ f) ^ 4 ≤ Nat.card S := by
  have hord := (symplectic_model_outer_two_part_bound S n p f h).1
  obtain ⟨hp, hf, hn, -⟩ := h.1
  set q := p ^ f
  have hq2 : 2 ≤ q := le_trans hp.two_le (by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf)
  have hn2 : 4 ≤ n ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
  have hq4 : q ^ 4 ≤ q ^ (n ^ 2) := Nat.pow_le_pow_right (by omega) hn2
  have hd : Nat.gcd 2 (q - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
  have h1mem : (1 : ℕ) ∈ Icc 1 n := mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hP : q ^ 2 - 1 ≤ ∏ j ∈ Icc 1 n, (q ^ (2 * j) - 1) := by
    calc q ^ 2 - 1 = q ^ (2 * 1) - 1 := by ring_nf
      _ ≤ ∏ j ∈ Icc 1 n, (q ^ (2 * j) - 1) :=
        Finset.single_le_prod (f := fun j => q ^ (2 * j) - 1) (fun j hj => by
          have : 2 ≤ q ^ (2 * j) := le_trans hq2 (by
            calc q = q ^ 1 := (pow_one q).symm
              _ ≤ q ^ (2 * j) := Nat.pow_le_pow_right (by omega) (by simp at hj; omega))
          omega) h1mem
  have hP3 : 3 ≤ ∏ j ∈ Icc 1 n, (q ^ (2 * j) - 1) := by
    have : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq2 2
    omega
  rw [hord]
  refine (Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_left _ (by norm_num))).mpr ?_
  calc q ^ 4 * Nat.gcd 2 (q - 1)
      ≤ q ^ (n ^ 2) * 2 := Nat.mul_le_mul hq4 hd
    _ ≤ q ^ (n ^ 2) * ∏ j ∈ Icc 1 n, (q ^ (2 * j) - 1) := Nat.mul_le_mul_left _ (by omega)

private theorem int_one_le_prod {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℤ}
    (hf : ∀ j ∈ s, 1 ≤ f j) : 1 ≤ ∏ j ∈ s, f j := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha1 := hf a (Finset.mem_insert_self a s)
    have hs1 := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    nlinarith

private theorem int_single_le_prod {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℤ}
    (hf : ∀ j ∈ s, 1 ≤ f j) {i : ι} (hi : i ∈ s) : f i ≤ ∏ j ∈ s, f j := by
  rw [← Finset.mul_prod_erase s f hi]
  have h1 : 1 ≤ ∏ j ∈ s.erase i, f j :=
    int_one_le_prod fun j hj => hf j (Finset.mem_of_mem_erase hj)
  exact le_mul_of_one_le_right (by have := hf i hi; omega) h1

/-- Lower bound `(p ^ f) ^ 3 ≤ Nat.card S` for `PSU(n, p^f)`. -/
theorem pow_three_le_card_of_psu {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSU n p f) :
    (p ^ f) ^ 3 ≤ Nat.card S := by
  have hexact := (unitary_model_outer_two_part_bound S n p f h).1
  obtain ⟨hp, hf, hn, -⟩ := h.1
  set q := p ^ f
  have hq2 : 2 ≤ q := le_trans hp.two_le (by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf)
  have hN3 : 3 ≤ n * (n - 1) / 2 := by
    have : 6 ≤ n * (n - 1) := le_trans (by norm_num : 6 ≤ 3 * 2) (Nat.mul_le_mul hn (by omega))
    omega
  have hqN : ((q : ℤ) ^ 3) ≤ (q : ℤ) ^ (n * (n - 1) / 2) :=
    pow_le_pow_right₀ (by omega) hN3
  have hd : (Nat.gcd n (q + 1) : ℤ) ≤ (q : ℤ) + 1 := by
    exact_mod_cast Nat.gcd_le_right n (by omega)
  have h3mem : (3 : ℕ) ∈ Icc 2 n := mem_Icc.mpr ⟨by norm_num, hn⟩
  have hpos : ∀ j ∈ Icc 2 n, (1 : ℤ) ≤ (q : ℤ) ^ j - (-1) ^ j := by
    intro j hj
    have hqj : (2 : ℤ) ≤ (q : ℤ) ^ j := by
      calc (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq2
        _ = (q : ℤ) ^ 1 := (pow_one _).symm
        _ ≤ (q : ℤ) ^ j := pow_le_pow_right₀ (by omega) (by simp at hj; omega)
    rcases neg_one_pow_eq_or ℤ j with h1 | h1 <;> rw [h1] <;> omega
  have hP : (q : ℤ) + 1 ≤ ∏ j ∈ Icc 2 n, ((q : ℤ) ^ j - (-1) ^ j) := by
    have h3 : (q : ℤ) ^ 3 - (-1) ^ 3 = (q : ℤ) ^ 3 + 1 := by ring
    have hq3 : (q : ℤ) + 1 ≤ (q : ℤ) ^ 3 + 1 := by
      have : (q : ℤ) ^ 1 ≤ (q : ℤ) ^ 3 := pow_le_pow_right₀ (by omega) (by norm_num)
      linarith [pow_one (q : ℤ)]
    exact hq3.trans (h3 ▸ int_single_le_prod hpos h3mem)
  have hmul : ((q ^ 3 : ℕ) : ℤ) * (Nat.gcd n (q + 1) : ℤ) ≤
      (Nat.card S : ℤ) * (Nat.gcd n (q + 1) : ℤ) := by
    rw [hexact, Nat.cast_pow]
    exact mul_le_mul hqN (hd.trans hP) (by positivity) (by positivity)
  have hd0 : (0 : ℤ) < (Nat.gcd n (q + 1) : ℤ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left _ (by omega)
  exact_mod_cast le_of_mul_le_mul_right hmul hd0

/-- For every finite group `S` satisfying `OtherClassicalSocle S`,
`Nat.card (OuterAut S) ≤ Nat.card S`. -/
theorem card_outerAut_le_card_of_otherClassicalSocle {S : Type} [Group S] [Finite S]
    (hS : OtherClassicalSocle S) :
    Nat.card (OuterAut S) ≤ Nat.card S := by
  obtain ⟨t, n, p, f, ht, h⟩ := hS
  set q := p ^ f
  cases t with
  | PSL => exact absurd rfl ht
  | PSU =>
    obtain ⟨hp, hf, hn, -⟩ := h.1
    have hq2 : 2 ≤ q := le_trans hp.two_le (by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf)
    have h2f : 2 * f ≤ q := two_mul_le_pow_of_two_le hp.two_le hf
    have hd : Nat.gcd n (q + 1) ≤ q + 1 := Nat.gcd_le_right n (by omega)
    rw [card_outerAut_psu_eq h]
    calc 2 * f * Nat.gcd n (q + 1)
        ≤ q * (q + 1) := Nat.mul_le_mul h2f hd
      _ ≤ q * (q * q) := Nat.mul_le_mul_left q (by nlinarith)
      _ = q ^ 3 := by ring
      _ ≤ Nat.card S := pow_three_le_card_of_psu h
  | PSp =>
    obtain ⟨hp, hf, hn, -⟩ := h.1
    have hq2 : 2 ≤ q := le_trans hp.two_le (by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf)
    have h2f : 2 * f ≤ q := two_mul_le_pow_of_two_le hp.two_le hf
    have hd : Nat.gcd 2 (q - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    have hdvd := card_outerAut_psp_dvd h
    have hpos : 0 < 2 * f * Nat.gcd 2 (q - 1) :=
      Nat.mul_pos (Nat.mul_pos two_pos hf) (Nat.gcd_pos_of_pos_left _ two_pos)
    calc Nat.card (OuterAut S)
        ≤ 2 * f * Nat.gcd 2 (q - 1) := Nat.le_of_dvd hpos hdvd
      _ ≤ q * 2 := Nat.mul_le_mul h2f hd
      _ ≤ q ^ 4 := by
        calc q * 2 ≤ q * q ^ 3 := Nat.mul_le_mul_left q (by
              calc 2 ≤ 2 ^ 3 := by norm_num
                _ ≤ q ^ 3 := Nat.pow_le_pow_left hq2 3)
          _ = q ^ 4 := by ring
      _ ≤ Nat.card S := pow_four_le_card_of_psp h
  | POmegaOdd =>
    obtain ⟨hp, hf, hn, -⟩ := h.1
    have hqpos : 0 < q := pow_pos hp.pos f
    have h2f : 2 * f ≤ q := two_mul_le_pow_of_two_le hp.two_le hf
    have hdvd := card_outerAut_pOmegaOdd_dvd h
    calc Nat.card (OuterAut S)
        ≤ 2 * f := Nat.le_of_dvd (by omega) hdvd
      _ ≤ q := h2f
      _ ≤ 21 * q ^ 3 := by
        have : q ^ 1 ≤ q ^ 3 := Nat.pow_le_pow_right hqpos (by norm_num)
        linarith [pow_one q]
      _ ≤ Nat.card S := pow_three_le_card_of_orthogonal (.inl rfl) h
  | POmegaPlus =>
    obtain ⟨hp, hf, hn⟩ := h.1
    have hqpos : 0 < q := pow_pos hp.pos f
    have h2f : 2 * f ≤ q := two_mul_le_pow_of_two_le hp.two_le hf
    have hdvd := card_outerAut_pOmegaPlus_dvd h
    have hd : Nat.gcd 4 (q ^ n - 1) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
    have hk : (if n = 4 then 6 else 2) ≤ 6 := by split_ifs <;> norm_num
    have hpos : 0 < Nat.gcd 4 (q ^ n - 1) * f * (if n = 4 then 6 else 2) :=
      Nat.mul_pos (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ (by norm_num)) hf)
        (by split_ifs <;> norm_num)
    calc Nat.card (OuterAut S)
        ≤ Nat.gcd 4 (q ^ n - 1) * f * (if n = 4 then 6 else 2) := Nat.le_of_dvd hpos hdvd
      _ ≤ 4 * f * 6 := Nat.mul_le_mul (Nat.mul_le_mul_right f hd) hk
      _ = 12 * (2 * f) := by ring
      _ ≤ 12 * q := Nat.mul_le_mul_left 12 h2f
      _ ≤ 21 * q ^ 3 := by
        have : q ^ 1 ≤ q ^ 3 := Nat.pow_le_pow_right hqpos (by norm_num)
        linarith [pow_one q]
      _ ≤ Nat.card S := pow_three_le_card_of_orthogonal (.inr (.inl rfl)) h
  | POmegaMinus =>
    obtain ⟨hp, hf, hn⟩ := h.1
    have hqpos : 0 < q := pow_pos hp.pos f
    have h2f : 2 * f ≤ q := two_mul_le_pow_of_two_le hp.two_le hf
    have hdvd := card_outerAut_pOmegaMinus_dvd h
    have hd : Nat.gcd 4 (q ^ n + 1) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
    have hpos : 0 < Nat.gcd 4 (q ^ n + 1) * f * 2 :=
      Nat.mul_pos (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ (by norm_num)) hf) two_pos
    calc Nat.card (OuterAut S)
        ≤ Nat.gcd 4 (q ^ n + 1) * f * 2 := Nat.le_of_dvd hpos hdvd
      _ ≤ 4 * f * 2 := Nat.mul_le_mul_right 2 (Nat.mul_le_mul_right f hd)
      _ = 4 * (2 * f) := by ring
      _ ≤ 4 * q := Nat.mul_le_mul_left 4 h2f
      _ ≤ 21 * q ^ 3 := by
        have : q ^ 1 ≤ q ^ 3 := Nat.pow_le_pow_right hqpos (by norm_num)
        linarith [pow_one q]
      _ ≤ Nat.card S := pow_three_le_card_of_orthogonal (.inr (.inr rfl)) h
  | _ => exact False.elim h.2

/-- Every finite group `S` with `OtherClassicalSocle S` satisfies
`Nat.card (MulAut S) ≤ Nat.card S ^ 2`. -/
theorem autBound_otherClassical : AutBound OtherClassicalSocle := by
  intro S _ _ hS
  calc Nat.card (MulAut S)
      ≤ Nat.card S * Nat.card (OuterAut S) := card_mulAut_le_card_mul_outerAut S
    _ ≤ Nat.card S * Nat.card S :=
      Nat.mul_le_mul_left (Nat.card S) (card_outerAut_le_card_of_otherClassicalSocle hS)
    _ = Nat.card S ^ 2 := (sq (Nat.card S)).symm

/-- Dispatch `AlmostSimpleCase OtherClassicalSocle` across the five classical Lie tags `PSU`,
`PSp`, `POmegaOdd`, `POmegaPlus`, and `POmegaMinus`. -/
theorem otherClassicalCase_of_tags (hU : AlmostSimpleCase (ClassicalSocle .PSU))
    (hSp : AlmostSimpleCase (ClassicalSocle .PSp))
    (hO : AlmostSimpleCase (ClassicalSocle .POmegaOdd))
    (hP : AlmostSimpleCase (ClassicalSocle .POmegaPlus))
    (hM : AlmostSimpleCase (ClassicalSocle .POmegaMinus)) :
    AlmostSimpleCase OtherClassicalSocle := by
  intro α _ G S _ hG hAS ⟨t, n, p, f, ht, h⟩
  cases t with
  | PSL => exact absurd rfl ht
  | PSU => exact hU α G S hG hAS ⟨n, p, f, h⟩
  | PSp => exact hSp α G S hG hAS ⟨n, p, f, h⟩
  | POmegaOdd => exact hO α G S hG hAS ⟨n, p, f, h⟩
  | POmegaPlus => exact hP α G S hG hAS ⟨n, p, f, h⟩
  | POmegaMinus => exact hM α G S hG hAS ⟨n, p, f, h⟩
  | _ => exact False.elim h.2

end Maroti
