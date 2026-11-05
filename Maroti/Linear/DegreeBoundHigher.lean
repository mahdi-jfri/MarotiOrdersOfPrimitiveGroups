module

public import Maroti.Linear.DegreeBoundTwo
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# General degree lower bounds for `PSL(t, q)` (`t ≥ 3`)

This file proves the general Heisenberg-torus degree lower bound `(Nat.card K) ^ (t - 1) ≤ H.index`
for any proper subgroup `H < projectiveSL t K` (`t ≥ 3`), together with the prime-divisor degree
bounds for `(t, q) = (3, 3)` and `(t, q) = (3, 2)`:

* The theorem `Maroti.isSimpleGroup_projectiveSL` shows that for `t ≥ 3`, `projectiveSL t K` is a
  simple group (via `CFSG.LinearGroups.linear_projective_simple` and
  `projectiveSpecialLinearEquivProjectiveSL`).
* The definitions `Maroti.qMat`, `Maroti.qSubgroup`, `Maroti.zSubgroup`, and `Maroti.qdSubgroup`
  construct the Heisenberg unipotent radical `Q` of order `q^(2t-3)` with center `Z` of order `q`
  and 1-parameter torus `D` of order `q - 1` inside `SL(t, K)`.
* The theorem `Maroti.card_pow_pred_le_index_of_ne_top` shows that for `t ≥ 3` and
  `H : Subgroup (projectiveSL t K)` with `H ≠ ⊤`, `(Nat.card K) ^ (t - 1) ≤ H.index`.
* The theorems `Maroti.thirteen_le_index_of_three_three` and `Maroti.seven_le_index_of_three_two`
  prove the prime-divisor degree bounds `13 ≤ H.index` for `PSL(3, 3)` and `7 ≤ H.index` for
  `PSL(3, 2)`.
-/

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace Maroti

open Subgroup Equiv Matrix Module
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

/-- For `t ≥ 3`, `projectiveSL t K` is a simple group. -/
theorem isSimpleGroup_projectiveSL {t : ℕ} (ht : 3 ≤ t) (K : Type*) [Field K] :
    IsSimpleGroup (projectiveSL t K) := by
  have _ : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin t) K) :=
    (CFSG.LinearGroups.linear_projective_simple (K := K) (n := t) (by omega) (Or.inl ht)).2.1
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL t K).symm.isSimpleGroup

/-- In a simple group `S`, the permutation action on the left cosets `S ⧸ H` of any proper subgroup
`H ≠ ⊤` is faithful. -/
theorem toPermHom_quotient_injective_of_ne_top {S : Type*} [Group S] [IsSimpleGroup S]
    {H : Subgroup S} (hH : H ≠ ⊤) :
    Function.Injective (MulAction.toPermHom S (S ⧸ H)) := by
  let φ := MulAction.toPermHom S (S ⧸ H)
  rw [← MonoidHom.ker_eq_bot_iff φ]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hbot | htop
  · exact hbot
  · exfalso
    apply hH
    rw [eq_top_iff]
    intro s _
    have hs : s ∈ φ.ker := htop ▸ Subgroup.mem_top s
    have hfix : s • (QuotientGroup.mk 1 : S ⧸ H) = QuotientGroup.mk 1 := by
      change (φ s) (QuotientGroup.mk 1) = QuotientGroup.mk 1
      rw [MonoidHom.mem_ker.mp hs, Perm.one_apply]
    have heq : (QuotientGroup.mk (s * 1) : S ⧸ H) = QuotientGroup.mk 1 := hfix
    rw [QuotientGroup.eq] at heq
    simpa using heq

/-- For any proper subgroup `H` and nontrivial subgroup `Z` of a simple group `S`, there exists
`g : S` such that `¬ (Z ≤ H.map (MulAut.conj g))`. -/
theorem exists_not_le_map_conj_of_ne_bot {S : Type*} [Group S] [IsSimpleGroup S]
    {H Z : Subgroup S} (hH : H ≠ ⊤) (hZ : Z ≠ ⊥) :
    ∃ g : S, ¬ (Z ≤ H.map (MulAut.conj g : S →* S)) := by
  have hex : ∃ z ∈ Z, z ≠ 1 := by
    by_contra! hall
    apply hZ
    rw [eq_bot_iff]
    intro z hz
    exact Subgroup.mem_bot.mpr (hall z hz)
  obtain ⟨z, hzZ, hz1⟩ := hex
  have hφ_inj := toPermHom_quotient_injective_of_ne_top hH
  have hφz : MulAction.toPermHom S (S ⧸ H) z ≠ 1 := fun h =>
    hz1 (hφ_inj (h.trans (map_one _).symm))
  have hmove : ∃ x : S ⧸ H, z • x ≠ x := by
    by_contra! hfix
    apply hφz
    ext x
    exact hfix x
  obtain ⟨x, hx⟩ := hmove
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨g, fun hle => hx ?_⟩
  obtain ⟨h, hhH, hgh⟩ := hle hzZ
  change QuotientGroup.mk (z * g) = QuotientGroup.mk g
  rw [QuotientGroup.eq]
  have heq : (z * g)⁻¹ * g = h⁻¹ := by
    have hgh' : g * h * g⁻¹ = z := hgh
    rw [← hgh']
    group
  rw [heq]
  exact H.inv_mem hhH

/-- First index `0` in `Fin t`. -/
@[expose]
def firstIdx (t : ℕ) [NeZero t] : Fin t :=
  ⟨0, NeZero.pos t⟩

/-- Last index `t - 1` in `Fin t`. -/
@[expose]
def lastIdx (t : ℕ) [NeZero t] : Fin t :=
  ⟨t - 1, Nat.sub_lt (NeZero.pos t) zero_lt_one⟩

@[simp]
theorem val_firstIdx (t : ℕ) [NeZero t] : (firstIdx t : ℕ) = 0 :=
  rfl

@[simp]
theorem val_lastIdx (t : ℕ) [NeZero t] : (lastIdx t : ℕ) = t - 1 :=
  rfl

theorem firstIdx_ne_lastIdx {t : ℕ} [NeZero t] (ht : 2 ≤ t) :
    firstIdx t ≠ lastIdx t := by
  intro h
  have := congrArg Fin.val h
  simp only [val_firstIdx, val_lastIdx] at this
  omega

/-- The middle indices `{1, ..., t - 2}` inside `Fin t`. -/
abbrev Mid (t : ℕ) [NeZero t] : Type :=
  {k : Fin t // k ≠ firstIdx t ∧ k ≠ lastIdx t}

/-- Explicit equivalence between `Fin (t - 2)` and `Mid t` for `t ≥ 2`. -/
@[expose]
def midEquiv {t : ℕ} [NeZero t] (ht : 2 ≤ t) : Fin (t - 2) ≃ Mid t where
  toFun k := ⟨⟨k.1 + 1, by omega⟩,
    ⟨fun h => by have := congrArg Fin.val h; simp at this,
     fun h => by have := congrArg Fin.val h; simp at this; omega⟩⟩
  invFun m := ⟨m.1.1 - 1, by
    have h1 : m.1.1 ≠ 0 := fun h => m.2.1 (Fin.ext h)
    have h2 : m.1.1 ≠ t - 1 := fun h => m.2.2 (Fin.ext h)
    have h3 : m.1.1 < t := m.1.2
    omega⟩
  left_inv k := by ext; simp
  right_inv m := by
    have h1 : m.1.1 ≠ 0 := fun h => m.2.1 (Fin.ext h)
    ext
    simp
    omega

theorem card_mid_fun {t : ℕ} [NeZero t] (ht : 2 ≤ t) (K : Type*) [Finite K] :
    Nat.card (Mid t → K) = Nat.card K ^ (t - 2) := by
  have := Fintype.ofFinite K
  rw [← Nat.card_congr (Equiv.arrowCongr (midEquiv ht) (Equiv.refl K)),
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card]

/-- Nilpotent matrix with top row `u`, right column `v`, and corner `z`. -/
@[expose]
def qNil {t : ℕ} [NeZero t] {K : Type*} [Field K] (u v : Mid t → K) (z : K) :
    Matrix (Fin t) (Fin t) K :=
  Matrix.of fun i j =>
    if i = firstIdx t then
      if j = lastIdx t then z
      else if hj : j ≠ firstIdx t ∧ j ≠ lastIdx t then u ⟨j, hj⟩
      else 0
    else if hi : i ≠ firstIdx t ∧ i ≠ lastIdx t then
      if j = lastIdx t then v ⟨i, hi⟩ else 0
    else 0

theorem qNil_apply {t : ℕ} [NeZero t] {K : Type*} [Field K] (u v : Mid t → K) (z : K)
    (i j : Fin t) :
    qNil u v z i j =
      if i = firstIdx t then
        if j = lastIdx t then z
        else if hj : j ≠ firstIdx t ∧ j ≠ lastIdx t then u ⟨j, hj⟩
        else 0
      else if hi : i ≠ firstIdx t ∧ i ≠ lastIdx t then
        if j = lastIdx t then v ⟨i, hi⟩ else 0
      else 0 :=
  rfl

theorem qNil_apply_of_le {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    (u v : Mid t → K) (z : K) {i j : Fin t} (hij : j ≤ i) :
    qNil u v z i j = 0 := by
  have hij' : (j : ℕ) ≤ (i : ℕ) := hij
  rw [qNil_apply]
  split_ifs with h1 h2 h3 h4 h5
  · exfalso
    rw [h1, h2, val_firstIdx, val_lastIdx] at hij'
    omega
  · exfalso
    rw [h1, val_firstIdx] at hij'
    have hj0 : (j : ℕ) = 0 := by omega
    exact h3.1 (Fin.ext hj0)
  · rfl
  · exfalso
    rw [h5, val_lastIdx] at hij'
    have hi_lt : (i : ℕ) < t := i.2
    have hit : (i : ℕ) = t - 1 := by omega
    exact h4.2 (Fin.ext hit)
  · rfl
  · rfl

@[simp]
theorem qNil_zero {t : ℕ} [NeZero t] {K : Type*} [Field K] :
    qNil (0 : Mid t → K) (0 : Mid t → K) (0 : K) = 0 := by
  ext i j
  rw [qNil_apply]
  split_ifs <;> rfl

theorem qNil_add {t : ℕ} [NeZero t] {K : Type*} [Field K]
    (u₁ v₁ u₂ v₂ : Mid t → K) (z₁ z₂ : K) :
    qNil u₁ v₁ z₁ + qNil u₂ v₂ z₂ = qNil (u₁ + u₂) (v₁ + v₂) (z₁ + z₂) := by
  ext i j
  rw [Matrix.add_apply, qNil_apply, qNil_apply, qNil_apply]
  split_ifs <;> simp [Pi.add_apply]

theorem qNil_neg {t : ℕ} [NeZero t] {K : Type*} [Field K] (u v : Mid t → K) (z : K) :
    -qNil u v z = qNil (-u) (-v) (-z) := by
  ext i j
  rw [Matrix.neg_apply, qNil_apply, qNil_apply]
  split_ifs <;> simp

theorem qNil_apply_firstIdx_right {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    (u v : Mid t → K) (z : K) (i : Fin t) :
    qNil u v z i (firstIdx t) = 0 :=
  qNil_apply_of_le ht u v z (Fin.zero_le i)

theorem qNil_apply_lastIdx_left {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    (u v : Mid t → K) (z : K) (j : Fin t) :
    qNil u v z (lastIdx t) j = 0 := by
  apply qNil_apply_of_le ht u v z
  rw [Fin.le_def, val_lastIdx]
  have := j.2
  omega

theorem qNil_apply_mid_right {t : ℕ} [NeZero t] {K : Type*} [Field K]
    (u v : Mid t → K) (z : K) (i : Fin t) (m : Mid t) :
    qNil u v z i m.1 = if i = firstIdx t then u m else 0 := by
  rw [qNil_apply]
  split_ifs with h1 h2 h3 h4 h5
  · exact absurd h2 m.2.2
  · rfl
  · exact absurd m.2 h3
  · exact absurd h5 m.2.2
  · rfl
  · rfl

theorem qNil_apply_mid_left {t : ℕ} [NeZero t] {K : Type*} [Field K]
    (u v : Mid t → K) (z : K) (m : Mid t) (j : Fin t) :
    qNil u v z m.1 j = if j = lastIdx t then v m else 0 := by
  rw [qNil_apply, ite_eq_right m.2.1, dite_eq_left m.2]

theorem qNil_mul_qNil {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    (u₁ v₁ u₂ v₂ : Mid t → K) (z₁ z₂ : K) :
    qNil u₁ v₁ z₁ * qNil u₂ v₂ z₂ = qNil 0 0 (u₁ ⬝ᵥ v₂) := by
  ext i j
  rw [Matrix.mul_apply, qNil_apply]
  have hterm : ∀ k : Fin t,
      qNil u₁ v₁ z₁ i k * qNil u₂ v₂ z₂ k j =
        if hk : k ≠ firstIdx t ∧ k ≠ lastIdx t then
          (if i = firstIdx t ∧ j = lastIdx t then u₁ ⟨k, hk⟩ * v₂ ⟨k, hk⟩ else 0)
        else 0 := by
    intro k
    by_cases hk : k ≠ firstIdx t ∧ k ≠ lastIdx t
    · rw [dite_eq_left hk, qNil_apply_mid_right u₁ v₁ z₁ i ⟨k, hk⟩,
        qNil_apply_mid_left u₂ v₂ z₂ ⟨k, hk⟩ j]
      by_cases hi : i = firstIdx t <;> by_cases hj : j = lastIdx t <;> simp [hi, hj]
    · rw [dite_eq_right hk]
      by_cases hk1 : k = firstIdx t
      · subst hk1
        rw [qNil_apply_firstIdx_right ht, zero_mul]
      · have hk2 : k = lastIdx t := by
          by_contra hk2
          exact hk ⟨hk1, hk2⟩
        subst hk2
        rw [qNil_apply_lastIdx_left ht, mul_zero]
  simp_rw [hterm]
  by_cases hij : i = firstIdx t ∧ j = lastIdx t
  · rcases hij with ⟨rfl, rfl⟩
    simp only [and_self, ↓reduceIte]
    rw [dotProduct, ← Finset.sum_subset (Finset.subset_univ
      ((Finset.univ : Finset (Mid t)).map ⟨Subtype.val, Subtype.val_injective⟩))]
    · rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun m _ => ?_
      exact dite_eq_left m.2
    · intro k _ hk_not
      rw [Finset.mem_map] at hk_not
      have hk' : ¬ (k ≠ firstIdx t ∧ k ≠ lastIdx t) := fun hk =>
        hk_not ⟨⟨k, hk⟩, Finset.mem_univ _, rfl⟩
      exact dite_eq_right hk'
  · have hzero : ∀ k : Fin t,
        (if hk : k ≠ firstIdx t ∧ k ≠ lastIdx t then
          if i = firstIdx t ∧ j = lastIdx t then u₁ ⟨k, hk⟩ * v₂ ⟨k, hk⟩ else 0
        else 0) = 0 := by
      intro k
      by_cases hk : k ≠ firstIdx t ∧ k ≠ lastIdx t <;> simp [hk, hij]
    rw [Finset.sum_eq_zero (fun k _ => hzero k)]
    split_ifs with h1 h2
    · exact absurd ⟨h1, h2⟩ hij
    all_goals rfl

theorem det_one_add_qNil {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    (u v : Mid t → K) (z : K) :
    (1 + qNil u v z).det = 1 := by
  rw [det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    rw [Matrix.add_apply, Matrix.one_apply_eq, qNil_apply_of_le ht u v z le_rfl, add_zero]
  · intro i j hij
    have hij' : j < i := hij
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij'),
      qNil_apply_of_le ht u v z hij'.le, add_zero]

/-- Heisenberg element `1 + qNil u v z` in `SpecialLinearGroup (Fin t) K`. -/
@[expose]
def qMat {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    (u v : Mid t → K) (z : K) : SpecialLinearGroup (Fin t) K :=
  ⟨1 + qNil u v z, det_one_add_qNil ht u v z⟩

@[simp]
theorem coe_qMat {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    (u v : Mid t → K) (z : K) :
    (qMat ht u v z : Matrix (Fin t) (Fin t) K) = 1 + qNil u v z :=
  rfl

theorem qMat_zero {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t) :
    qMat ht (0 : Mid t → K) (0 : Mid t → K) (0 : K) = 1 := by
  apply Subtype.ext
  change 1 + qNil (0 : Mid t → K) 0 0 = 1
  rw [qNil_zero, add_zero]

theorem qMat_mul {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    (u₁ v₁ u₂ v₂ : Mid t → K) (z₁ z₂ : K) :
    qMat ht u₁ v₁ z₁ * qMat ht u₂ v₂ z₂ =
      qMat ht (u₁ + u₂) (v₁ + v₂) (z₁ + z₂ + u₁ ⬝ᵥ v₂) := by
  apply Subtype.ext
  change (1 + qNil u₁ v₁ z₁) * (1 + qNil u₂ v₂ z₂) =
    1 + qNil (u₁ + u₂) (v₁ + v₂) (z₁ + z₂ + u₁ ⬝ᵥ v₂)
  calc (1 + qNil u₁ v₁ z₁) * (1 + qNil u₂ v₂ z₂)
    _ = 1 + (qNil u₁ v₁ z₁ + qNil u₂ v₂ z₂ + qNil u₁ v₁ z₁ * qNil u₂ v₂ z₂) := by
        noncomm_ring
    _ = 1 + (qNil (u₁ + u₂) (v₁ + v₂) (z₁ + z₂) + qNil 0 0 (u₁ ⬝ᵥ v₂)) := by
        rw [qNil_add, qNil_mul_qNil ht]
    _ = 1 + qNil (u₁ + u₂) (v₁ + v₂) (z₁ + z₂ + u₁ ⬝ᵥ v₂) := by
        rw [qNil_add, add_zero, add_zero]

theorem qMat_inv {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    (u v : Mid t → K) (z : K) :
    (qMat ht u v z)⁻¹ = qMat ht (-u) (-v) (-z + u ⬝ᵥ v) := by
  rw [inv_eq_iff_mul_eq_one, qMat_mul]
  have h1 : u + -u = 0 := add_neg_cancel u
  have h2 : v + -v = 0 := add_neg_cancel v
  have h3 : z + (-z + u ⬝ᵥ v) + u ⬝ᵥ -v = 0 := by
    rw [dotProduct_neg]
    ring
  rw [h1, h2, h3, qMat_zero]

theorem qMat_conj {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    (u₁ v₁ u₂ v₂ : Mid t → K) (z₁ z₂ : K) :
    qMat ht u₁ v₁ z₁ * qMat ht u₂ v₂ z₂ * (qMat ht u₁ v₁ z₁)⁻¹ =
      qMat ht u₂ v₂ (z₂ + (u₁ ⬝ᵥ v₂ - u₂ ⬝ᵥ v₁)) := by
  rw [qMat_inv, qMat_mul, qMat_mul]
  congr 1
  · abel
  · abel
  · simp only [add_dotProduct, dotProduct_neg]
    ring

theorem qMat_apply_firstIdx_lastIdx {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    (u v : Mid t → K) (z : K) :
    (qMat ht u v z : Matrix (Fin t) (Fin t) K) (firstIdx t) (lastIdx t) = z := by
  rw [coe_qMat, Matrix.add_apply, Matrix.one_apply_ne (firstIdx_ne_lastIdx ht), zero_add,
    qNil_apply]
  simp

theorem qMat_apply_firstIdx_mid {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    (u v : Mid t → K) (z : K) (m : Mid t) :
    (qMat ht u v z : Matrix (Fin t) (Fin t) K) (firstIdx t) m.1 = u m := by
  rw [coe_qMat, Matrix.add_apply, Matrix.one_apply_ne m.2.1.symm, zero_add,
    qNil_apply_mid_right, ite_eq_left rfl]

theorem qMat_apply_mid_lastIdx {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    (u v : Mid t → K) (z : K) (m : Mid t) :
    (qMat ht u v z : Matrix (Fin t) (Fin t) K) m.1 (lastIdx t) = v m := by
  rw [coe_qMat, Matrix.add_apply, Matrix.one_apply_ne m.2.2, zero_add,
    qNil_apply_mid_left, ite_eq_left rfl]

theorem qMat_apply_diag {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    (u v : Mid t → K) (z : K) (i : Fin t) :
    (qMat ht u v z : Matrix (Fin t) (Fin t) K) i i = 1 := by
  rw [coe_qMat, Matrix.add_apply, Matrix.one_apply_eq, qNil_apply_of_le ht u v z le_rfl, add_zero]

theorem qMat_injective {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    {u₁ v₁ u₂ v₂ : Mid t → K} {z₁ z₂ : K}
    (h : qMat ht u₁ v₁ z₁ = qMat ht u₂ v₂ z₂) :
    u₁ = u₂ ∧ v₁ = v₂ ∧ z₁ = z₂ := by
  refine ⟨funext fun m => ?_, funext fun m => ?_, ?_⟩
  · rw [← qMat_apply_firstIdx_mid ht u₁ v₁ z₁ m, h, qMat_apply_firstIdx_mid]
  · rw [← qMat_apply_mid_lastIdx ht u₁ v₁ z₁ m, h, qMat_apply_mid_lastIdx]
  · rw [← qMat_apply_firstIdx_lastIdx ht u₁ v₁ z₁, h, qMat_apply_firstIdx_lastIdx]

theorem qMat_mem_unitriangular {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    (u v : Mid t → K) (z : K) :
    qMat ht u v z ∈ unitriangular t K := by
  refine ⟨fun i j hij => ?_, qMat_apply_diag ht u v z⟩
  rw [coe_qMat, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij),
    qNil_apply_of_le ht u v z hij.le, add_zero]

/-- The central root subgroup `Z = {qMat 0 0 z | z : K}` inside `SL(t, K)`. -/
@[expose]
def zSubgroup {t : ℕ} [NeZero t] (ht : 2 ≤ t) (K : Type*) [Field K] :
    Subgroup (SpecialLinearGroup (Fin t) K) where
  carrier := {g | ∃ z : K, g = qMat ht 0 0 z}
  one_mem' := ⟨0, (qMat_zero ht).symm⟩
  mul_mem' := by
    rintro _ _ ⟨z₁, rfl⟩ ⟨z₂, rfl⟩
    refine ⟨z₁ + z₂, ?_⟩
    rw [qMat_mul, add_zero, zero_dotProduct, add_zero]
  inv_mem' := by
    rintro _ ⟨z, rfl⟩
    refine ⟨-z, ?_⟩
    rw [qMat_inv, neg_zero, zero_dotProduct, add_zero]

/-- The Heisenberg subgroup `Q = {qMat u v z | u, v, z}` inside `SL(t, K)`. -/
@[expose]
def qSubgroup {t : ℕ} [NeZero t] (ht : 2 ≤ t) (K : Type*) [Field K] :
    Subgroup (SpecialLinearGroup (Fin t) K) where
  carrier := {g | ∃ (u v : Mid t → K) (z : K), g = qMat ht u v z}
  one_mem' := ⟨0, 0, 0, (qMat_zero ht).symm⟩
  mul_mem' := by
    rintro _ _ ⟨u₁, v₁, z₁, rfl⟩ ⟨u₂, v₂, z₂, rfl⟩
    exact ⟨u₁ + u₂, v₁ + v₂, z₁ + z₂ + u₁ ⬝ᵥ v₂, qMat_mul ht u₁ v₁ u₂ v₂ z₁ z₂⟩
  inv_mem' := by
    rintro _ ⟨u, v, z, rfl⟩
    exact ⟨-u, -v, -z + u ⬝ᵥ v, qMat_inv ht u v z⟩

theorem zSubgroup_le_qSubgroup {t : ℕ} [NeZero t] (ht : 2 ≤ t) (K : Type*) [Field K] :
    zSubgroup ht K ≤ qSubgroup ht K := by
  rintro g ⟨z, rfl⟩
  exact ⟨0, 0, z, rfl⟩

/-- Explicit equivalence between `(Mid t → K) × (Mid t → K) × K` and `qSubgroup ht K`. -/
@[expose]
def qSubgroupEquiv {t : ℕ} [NeZero t] (ht : 2 ≤ t) (K : Type*) [Field K] :
    ((Mid t → K) × (Mid t → K)) × K ≃ qSubgroup ht K where
  toFun p := ⟨qMat ht p.1.1 p.1.2 p.2, p.1.1, p.1.2, p.2, rfl⟩
  invFun g :=
    ((fun m => (g.1 : Matrix (Fin t) (Fin t) K) (firstIdx t) m.1,
      fun m => (g.1 : Matrix (Fin t) (Fin t) K) m.1 (lastIdx t)),
     (g.1 : Matrix (Fin t) (Fin t) K) (firstIdx t) (lastIdx t))
  left_inv p := by
    ext m
    · exact qMat_apply_firstIdx_mid ht p.1.1 p.1.2 p.2 m
    · exact qMat_apply_mid_lastIdx ht p.1.1 p.1.2 p.2 m
    · exact qMat_apply_firstIdx_lastIdx ht p.1.1 p.1.2 p.2
  right_inv g := by
    obtain ⟨_, u, v, z, rfl⟩ := g
    apply Subtype.ext
    change qMat ht _ _ _ = qMat ht u v z
    congr 1
    · funext m; exact qMat_apply_firstIdx_mid ht u v z m
    · funext m; exact qMat_apply_mid_lastIdx ht u v z m
    · exact qMat_apply_firstIdx_lastIdx ht u v z

theorem card_qSubgroup {t : ℕ} [NeZero t] (ht : 2 ≤ t) (K : Type*) [Field K] [Finite K] :
    Nat.card (qSubgroup ht K) = Nat.card K ^ (2 * t - 3) := by
  rw [← Nat.card_congr (qSubgroupEquiv ht K), Nat.card_prod, Nat.card_prod, card_mid_fun ht]
  calc (Nat.card K ^ (t - 2) * Nat.card K ^ (t - 2)) * Nat.card K
    _ = Nat.card K ^ ((t - 2) + (t - 2) + 1) := by rw [← pow_add, ← pow_succ]
    _ = Nat.card K ^ (2 * t - 3) := by congr 1; omega

/-- Diagonal vector with `a` at `0`, `a⁻¹` at `1`, and `1` elsewhere (`t ≥ 3`). -/
@[expose]
def dVec {t : ℕ} (_ht : 3 ≤ t) {K : Type*} [Field K] (a : Kˣ) (i : Fin t) : K :=
  if (i : ℕ) = 0 then (a : K)
  else if (i : ℕ) = 1 then ((a⁻¹ : Kˣ) : K)
  else 1

theorem dVec_one {t : ℕ} (ht : 3 ≤ t) {K : Type*} [Field K] :
    dVec ht (1 : Kˣ) = fun _ => 1 := by
  funext i
  simp [dVec]

theorem dVec_mul {t : ℕ} (ht : 3 ≤ t) {K : Type*} [Field K] (a b : Kˣ) (i : Fin t) :
    dVec ht a i * dVec ht b i = dVec ht (a * b) i := by
  dsimp [dVec]
  split_ifs <;> simp [mul_comm]

theorem det_diagonal_dVec {t : ℕ} (ht : 3 ≤ t) {K : Type*} [Field K] (a : Kˣ) :
    (diagonal (dVec ht a)).det = 1 := by
  rw [det_diagonal]
  let i₀ : Fin t := ⟨0, by omega⟩
  let i₁ : Fin t := ⟨1, by omega⟩
  have h01 : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  rw [← Finset.mul_prod_erase Finset.univ (dVec ht a) (Finset.mem_univ i₀)]
  have hi₁_mem : i₁ ∈ Finset.univ.erase i₀ :=
    Finset.mem_erase.mpr ⟨h01, Finset.mem_univ i₁⟩
  rw [← Finset.mul_prod_erase (Finset.univ.erase i₀) (dVec ht a) hi₁_mem]
  have hrest : ∏ x ∈ (Finset.univ.erase i₀).erase i₁, dVec ht a x = 1 := by
    refine Finset.prod_eq_one fun x hx => ?_
    simp only [Finset.mem_erase] at hx
    have hx1 : (x : ℕ) ≠ 1 := fun h => hx.1 (Fin.ext h)
    have hx0 : (x : ℕ) ≠ 0 := fun h => hx.2.1 (Fin.ext h)
    simp [dVec, hx0, hx1]
  rw [hrest, mul_one]
  change (a : K) * ((a⁻¹ : Kˣ) : K) = 1
  exact Units.mul_inv a

/-- Diagonal 1-parameter torus element `dMat ht a` in `SL(t, K)` (`t ≥ 3`). -/
@[expose]
def dMat {t : ℕ} (ht : 3 ≤ t) {K : Type*} [Field K] (a : Kˣ) :
    SpecialLinearGroup (Fin t) K :=
  ⟨diagonal (dVec ht a), det_diagonal_dVec ht a⟩

@[simp]
theorem coe_dMat {t : ℕ} (ht : 3 ≤ t) {K : Type*} [Field K] (a : Kˣ) :
    (dMat ht a : Matrix (Fin t) (Fin t) K) = diagonal (dVec ht a) :=
  rfl

theorem dMat_one {t : ℕ} (ht : 3 ≤ t) {K : Type*} [Field K] :
    dMat ht (1 : Kˣ) = 1 := by
  apply Subtype.ext
  change diagonal (dVec ht (1 : Kˣ)) = 1
  rw [dVec_one, diagonal_one]

theorem dMat_mul {t : ℕ} (ht : 3 ≤ t) {K : Type*} [Field K] (a b : Kˣ) :
    dMat ht a * dMat ht b = dMat ht (a * b) := by
  apply Subtype.ext
  change diagonal (dVec ht a) * diagonal (dVec ht b) = diagonal (dVec ht (a * b))
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  exact dVec_mul ht a b i

theorem dMat_inv {t : ℕ} (ht : 3 ≤ t) {K : Type*} [Field K] (a : Kˣ) :
    (dMat ht a)⁻¹ = dMat ht a⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, dMat_mul, mul_inv_cancel, dMat_one]

theorem dVec_firstIdx {t : ℕ} [NeZero t] (ht : 3 ≤ t) {K : Type*} [Field K] (a : Kˣ) :
    dVec ht a (firstIdx t) = (a : K) :=
  rfl

theorem dVec_lastIdx {t : ℕ} [NeZero t] (ht : 3 ≤ t) {K : Type*} [Field K] (a : Kˣ) :
    dVec ht a (lastIdx t) = 1 := by
  change (if (lastIdx t : ℕ) = 0 then (a : K)
    else if (lastIdx t : ℕ) = 1 then ((a⁻¹ : Kˣ) : K) else 1) = 1
  rw [ite_eq_right (by simp; omega), ite_eq_right (by simp; omega)]

theorem dMat_conj_qMat {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 3 ≤ t)
    (a : Kˣ) (u v : Mid t → K) (z : K) :
    dMat ht a * qMat (by omega : 2 ≤ t) u v z * (dMat ht a)⁻¹ =
      qMat (by omega : 2 ≤ t)
        (fun m => (a : K) * u m * dVec ht a⁻¹ m.1)
        (fun m => dVec ht a m.1 * v m)
        ((a : K) * z) := by
  rw [dMat_inv]
  have hd_mul : dMat ht a * dMat ht a⁻¹ = 1 := by
    rw [dMat_mul, mul_inv_cancel, dMat_one]
  have hdiag_inv : diagonal (dVec ht a) * diagonal (dVec ht a⁻¹) = 1 :=
    congrArg Subtype.val hd_mul
  apply Subtype.ext
  change diagonal (dVec ht a) * (1 + qNil u v z) * diagonal (dVec ht a⁻¹) =
    1 + qNil (fun m => (a : K) * u m * dVec ht a⁻¹ m.1)
      (fun m => dVec ht a m.1 * v m) ((a : K) * z)
  calc diagonal (dVec ht a) * (1 + qNil u v z) * diagonal (dVec ht a⁻¹)
    _ = diagonal (dVec ht a) * diagonal (dVec ht a⁻¹) +
        diagonal (dVec ht a) * qNil u v z * diagonal (dVec ht a⁻¹) := by
        noncomm_ring
    _ = 1 + diagonal (dVec ht a) * qNil u v z * diagonal (dVec ht a⁻¹) := by
        rw [hdiag_inv]
    _ = 1 + qNil (fun m => (a : K) * u m * dVec ht a⁻¹ m.1)
        (fun m => dVec ht a m.1 * v m) ((a : K) * z) := by
        congr 1
        ext i j
        rw [Matrix.mul_diagonal, Matrix.diagonal_mul, qNil_apply, qNil_apply]
        split_ifs with h1 h2 h3 h4 h5
        · rw [h1, h2, dVec_firstIdx, dVec_lastIdx, mul_one]
        · rw [h1, dVec_firstIdx]
        · ring
        · rw [h5, dVec_lastIdx, mul_one]
        · ring
        · ring

theorem qMat_dMat_conj_z {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 3 ≤ t)
    (u₀ v₀ : Mid t → K) (z₀ : K) (a : Kˣ) (w : K) :
    (qMat (by omega : 2 ≤ t) u₀ v₀ z₀ * dMat ht a) *
      qMat (by omega : 2 ≤ t) 0 0 w *
      (qMat (by omega : 2 ≤ t) u₀ v₀ z₀ * dMat ht a)⁻¹ =
      qMat (by omega : 2 ≤ t) 0 0 ((a : K) * w) := by
  have h01 : (fun m : Mid t => (a : K) * (0 : Mid t → K) m * dVec ht a⁻¹ m.1) = 0 := by
    funext m; simp
  have h02 : (fun m : Mid t => dVec ht a m.1 * (0 : Mid t → K) m) = 0 := by
    funext m; simp
  calc (qMat (by omega : 2 ≤ t) u₀ v₀ z₀ * dMat ht a) *
        qMat (by omega : 2 ≤ t) 0 0 w *
        (qMat (by omega : 2 ≤ t) u₀ v₀ z₀ * dMat ht a)⁻¹
    _ = qMat (by omega : 2 ≤ t) u₀ v₀ z₀ *
        (dMat ht a * qMat (by omega : 2 ≤ t) 0 0 w * (dMat ht a)⁻¹) *
        (qMat (by omega : 2 ≤ t) u₀ v₀ z₀)⁻¹ := by group
    _ = qMat (by omega : 2 ≤ t) u₀ v₀ z₀ *
        qMat (by omega : 2 ≤ t) 0 0 ((a : K) * w) *
        (qMat (by omega : 2 ≤ t) u₀ v₀ z₀)⁻¹ := by
        rw [dMat_conj_qMat, h01, h02]
    _ = qMat (by omega : 2 ≤ t) 0 0 ((a : K) * w) := by
        rw [qMat_conj]
        simp

/-- The semidirect product `QD = Q ⋊ D` inside `SL(t, K)` (`t ≥ 3`). -/
@[expose]
def qdSubgroup {t : ℕ} [NeZero t] (ht : 3 ≤ t) (K : Type*) [Field K] :
    Subgroup (SpecialLinearGroup (Fin t) K) where
  carrier := {g | ∃ (u v : Mid t → K) (z : K) (a : Kˣ),
    g = qMat (by omega : 2 ≤ t) u v z * dMat ht a}
  one_mem' := ⟨0, 0, 0, 1, by rw [qMat_zero, dMat_one, one_mul]⟩
  mul_mem' := by
    rintro _ _ ⟨u₁, v₁, z₁, a₁, rfl⟩ ⟨u₂, v₂, z₂, a₂, rfl⟩
    have hconj := dMat_conj_qMat ht a₁ u₂ v₂ z₂
    set u₂' : Mid t → K := fun m => (a₁ : K) * u₂ m * dVec ht a₁⁻¹ m.1
    set v₂' : Mid t → K := fun m => dVec ht a₁ m.1 * v₂ m
    set z₂' : K := (a₁ : K) * z₂
    have hcomm : dMat ht a₁ * qMat (by omega : 2 ≤ t) u₂ v₂ z₂ =
        qMat (by omega : 2 ≤ t) u₂' v₂' z₂' * dMat ht a₁ := by
      rw [← hconj, inv_mul_cancel_right]
    refine ⟨u₁ + u₂', v₁ + v₂', z₁ + z₂' + u₁ ⬝ᵥ v₂', a₁ * a₂, ?_⟩
    calc (qMat (by omega : 2 ≤ t) u₁ v₁ z₁ * dMat ht a₁) *
          (qMat (by omega : 2 ≤ t) u₂ v₂ z₂ * dMat ht a₂)
      _ = qMat (by omega : 2 ≤ t) u₁ v₁ z₁ *
          (dMat ht a₁ * qMat (by omega : 2 ≤ t) u₂ v₂ z₂) * dMat ht a₂ := by group
      _ = (qMat (by omega : 2 ≤ t) u₁ v₁ z₁ * qMat (by omega : 2 ≤ t) u₂' v₂' z₂') *
          (dMat ht a₁ * dMat ht a₂) := by
          rw [hcomm]
          group
      _ = qMat (by omega : 2 ≤ t) (u₁ + u₂') (v₁ + v₂') (z₁ + z₂' + u₁ ⬝ᵥ v₂') *
          dMat ht (a₁ * a₂) := by
          rw [qMat_mul, dMat_mul]
  inv_mem' := by
    rintro _ ⟨u, v, z, a, rfl⟩
    set q' := (qMat (by omega : 2 ≤ t) u v z)⁻¹
    obtain ⟨u', v', z', hq'⟩ : ∃ u' v' z', q' = qMat (by omega : 2 ≤ t) u' v' z' :=
      ⟨-u, -v, -z + u ⬝ᵥ v, qMat_inv (by omega : 2 ≤ t) u v z⟩
    have hconj := dMat_conj_qMat ht a⁻¹ u' v' z'
    set u'' : Mid t → K := fun m => ((a⁻¹ : Kˣ) : K) * u' m * dVec ht a⁻¹⁻¹ m.1
    set v'' : Mid t → K := fun m => dVec ht a⁻¹ m.1 * v' m
    set z'' : K := ((a⁻¹ : Kˣ) : K) * z'
    refine ⟨u'', v'', z'', a⁻¹, ?_⟩
    calc (qMat (by omega : 2 ≤ t) u v z * dMat ht a)⁻¹
      _ = (dMat ht a)⁻¹ * q' := mul_inv_rev _ _
      _ = (dMat ht a⁻¹ * qMat (by omega : 2 ≤ t) u' v' z' * (dMat ht a⁻¹)⁻¹) *
          dMat ht a⁻¹ := by
          rw [hq', dMat_inv]
          group
      _ = qMat (by omega : 2 ≤ t) u'' v'' z'' * dMat ht a⁻¹ := by
          rw [hconj]

theorem qSubgroup_le_qdSubgroup {t : ℕ} [NeZero t] (ht : 3 ≤ t) (K : Type*) [Field K] :
    qSubgroup (by omega : 2 ≤ t) K ≤ qdSubgroup ht K := by
  rintro _ ⟨u, v, z, rfl⟩
  exact ⟨u, v, z, 1, by rw [dMat_one, mul_one]⟩

theorem qMat_dMat_apply_firstIdx_self {t : ℕ} [NeZero t] (ht : 3 ≤ t) {K : Type*} [Field K]
    (u v : Mid t → K) (z : K) (a : Kˣ) :
    (qMat (by omega : 2 ≤ t) u v z * dMat ht a).1 (firstIdx t) (firstIdx t) = (a : K) := by
  change ((1 + qNil u v z) * diagonal (dVec ht a)) (firstIdx t) (firstIdx t) = (a : K)
  rw [Matrix.mul_diagonal, Matrix.add_apply, Matrix.one_apply_eq,
    qNil_apply_of_le (by omega : 2 ≤ t) u v z le_rfl, add_zero, one_mul, dVec_firstIdx]

/-- Explicit equivalence between `qSubgroup × Kˣ` and `qdSubgroup ht K`. -/
@[expose]
def qdSubgroupEquiv {t : ℕ} [NeZero t] (ht : 3 ≤ t) (K : Type*) [Field K] :
    qSubgroup (by omega : 2 ≤ t) K × Kˣ ≃ qdSubgroup ht K where
  toFun p := ⟨p.1.1 * dMat ht p.2, by
    obtain ⟨_, u, v, z, rfl⟩ := p.1
    exact ⟨u, v, z, p.2, rfl⟩⟩
  invFun g :=
    have hex : ∃ a : Kˣ, g.1.1 (firstIdx t) (firstIdx t) = (a : K) := by
      obtain ⟨_, u, v, z, a, rfl⟩ := g
      exact ⟨a, qMat_dMat_apply_firstIdx_self ht u v z a⟩
    let a : Kˣ := Units.mk0 (g.1.1 (firstIdx t) (firstIdx t))
      (by obtain ⟨a₀, ha₀⟩ := hex; rw [ha₀]; exact a₀.ne_zero)
    (⟨g.1 * (dMat ht a)⁻¹, by
      obtain ⟨_, u, v, z, a₀, rfl⟩ := g
      have ha_eq : a = a₀ := Units.ext (qMat_dMat_apply_firstIdx_self ht u v z a₀)
      rw [ha_eq, mul_inv_cancel_right]
      exact ⟨u, v, z, rfl⟩⟩, a)
  left_inv p := by
    obtain ⟨⟨_, u, v, z, rfl⟩, a⟩ := p
    have ha_eq : Units.mk0 ((qMat (by omega : 2 ≤ t) u v z * dMat ht a).1
        (firstIdx t) (firstIdx t))
        (by rw [qMat_dMat_apply_firstIdx_self]; exact a.ne_zero) = a :=
      Units.ext (qMat_dMat_apply_firstIdx_self ht u v z a)
    apply Prod.ext
    · apply Subtype.ext
      change qMat (by omega : 2 ≤ t) u v z * dMat ht a * (dMat ht _)⁻¹ =
        qMat (by omega : 2 ≤ t) u v z
      rw [ha_eq, mul_inv_cancel_right]
    · exact ha_eq
  right_inv g := by
    apply Subtype.ext
    change g.1 * (dMat ht _)⁻¹ * dMat ht _ = g.1
    exact inv_mul_cancel_right _ _

theorem card_qdSubgroup {t : ℕ} [NeZero t] (ht : 3 ≤ t) (K : Type*) [Field K] [Finite K] :
    Nat.card (qdSubgroup ht K) = Nat.card K ^ (2 * t - 3) * (Nat.card K - 1) := by
  rw [← Nat.card_congr (qdSubgroupEquiv ht K), Nat.card_prod, card_qSubgroup, Nat.card_units]

/-- Projection from `qdSubgroup ht K` to `Kˣ`. -/
@[expose]
def qdDiagHom {t : ℕ} [NeZero t] (ht : 3 ≤ t) (K : Type*) [Field K] :
    qdSubgroup ht K →* Kˣ where
  toFun g := ((qdSubgroupEquiv ht K).symm g).2
  map_one' := by
    have h1 : (1 : qdSubgroup ht K) = qdSubgroupEquiv ht K (1, 1) := by
      apply Subtype.ext
      change (1 : SpecialLinearGroup (Fin t) K) = (1 : SpecialLinearGroup (Fin t) K) * dMat ht 1
      rw [dMat_one, mul_one]
    rw [h1, Equiv.symm_apply_apply]
  map_mul' g₁ g₂ := by
    obtain ⟨⟨⟨_, u₁, v₁, z₁, rfl⟩, a₁⟩, rfl⟩ := (qdSubgroupEquiv ht K).surjective g₁
    obtain ⟨⟨⟨_, u₂, v₂, z₂, rfl⟩, a₂⟩, rfl⟩ := (qdSubgroupEquiv ht K).surjective g₂
    set u₂' : Mid t → K := fun m => (a₁ : K) * u₂ m * dVec ht a₁⁻¹ m.1
    set v₂' : Mid t → K := fun m => dVec ht a₁ m.1 * v₂ m
    set z₂' : K := (a₁ : K) * z₂
    have hcomm : dMat ht a₁ * qMat (by omega : 2 ≤ t) u₂ v₂ z₂ =
        qMat (by omega : 2 ≤ t) u₂' v₂' z₂' * dMat ht a₁ := by
      rw [← dMat_conj_qMat ht a₁ u₂ v₂ z₂, inv_mul_cancel_right]
    have hmul : qdSubgroupEquiv ht K (⟨qMat (by omega : 2 ≤ t) u₁ v₁ z₁, u₁, v₁, z₁, rfl⟩, a₁) *
        qdSubgroupEquiv ht K (⟨qMat (by omega : 2 ≤ t) u₂ v₂ z₂, u₂, v₂, z₂, rfl⟩, a₂) =
        qdSubgroupEquiv ht K
          (⟨qMat (by omega : 2 ≤ t) (u₁ + u₂') (v₁ + v₂') (z₁ + z₂' + u₁ ⬝ᵥ v₂'),
            u₁ + u₂', v₁ + v₂', z₁ + z₂' + u₁ ⬝ᵥ v₂', rfl⟩, a₁ * a₂) := by
      apply Subtype.ext
      change (qMat (by omega : 2 ≤ t) u₁ v₁ z₁ * dMat ht a₁) *
        (qMat (by omega : 2 ≤ t) u₂ v₂ z₂ * dMat ht a₂) =
        qMat (by omega : 2 ≤ t) (u₁ + u₂') (v₁ + v₂') (z₁ + z₂' + u₁ ⬝ᵥ v₂') * dMat ht (a₁ * a₂)
      calc (qMat (by omega : 2 ≤ t) u₁ v₁ z₁ * dMat ht a₁) *
            (qMat (by omega : 2 ≤ t) u₂ v₂ z₂ * dMat ht a₂)
        _ = qMat (by omega : 2 ≤ t) u₁ v₁ z₁ *
            (dMat ht a₁ * qMat (by omega : 2 ≤ t) u₂ v₂ z₂) * dMat ht a₂ := by group
        _ = (qMat (by omega : 2 ≤ t) u₁ v₁ z₁ * qMat (by omega : 2 ≤ t) u₂' v₂' z₂') *
            (dMat ht a₁ * dMat ht a₂) := by
            rw [hcomm]
            group
        _ = _ := by rw [qMat_mul, dMat_mul]
    rw [hmul, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Additive subgroup `{z : K | qMat ht 0 0 z ∈ H}` for
`H : Subgroup (SpecialLinearGroup (Fin t) K)`. -/
@[expose]
def zAddSubgroup {t : ℕ} [NeZero t] (ht : 2 ≤ t) {K : Type*} [Field K]
    (H : Subgroup (SpecialLinearGroup (Fin t) K)) : AddSubgroup K where
  carrier := {z : K | qMat ht 0 0 z ∈ H}
  zero_mem' := by
    change qMat ht 0 0 0 ∈ H
    rw [qMat_zero]
    exact H.one_mem
  add_mem' := fun {z₁ z₂} hz₁ hz₂ => by
    change qMat ht 0 0 (z₁ + z₂) ∈ H
    have heq : qMat ht 0 0 (z₁ + z₂) = qMat ht 0 0 z₁ * qMat ht 0 0 z₂ := by
      rw [qMat_mul, add_zero, zero_dotProduct, add_zero]
    rw [heq]
    exact H.mul_mem hz₁ hz₂
  neg_mem' := fun {z} hz => by
    change qMat ht 0 0 (-z) ∈ H
    have heq : qMat ht 0 0 (-z) = (qMat ht 0 0 z)⁻¹ := by
      rw [qMat_inv, neg_zero, zero_dotProduct, add_zero]
    rw [heq]
    exact H.inv_mem hz

/-- Additive subgroup `{(u, v) | ∃ z, qMat ht u v z ∈ H}` inside `(Mid t → K) × (Mid t → K)`. -/
@[expose]
def eAddSubgroup {t : ℕ} [NeZero t] (ht : 2 ≤ t) {K : Type*} [Field K]
    (H : Subgroup (SpecialLinearGroup (Fin t) K)) :
    AddSubgroup ((Mid t → K) × (Mid t → K)) where
  carrier := {x | ∃ z : K, qMat ht x.1 x.2 z ∈ H}
  zero_mem' := ⟨0, by rw [Prod.fst_zero, Prod.snd_zero, qMat_zero]; exact H.one_mem⟩
  add_mem' := by
    rintro x y ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
    refine ⟨z₁ + z₂ + x.1 ⬝ᵥ y.2, ?_⟩
    rw [Prod.fst_add, Prod.snd_add, ← qMat_mul]
    exact H.mul_mem hz₁ hz₂
  neg_mem' := by
    rintro x ⟨z, hz⟩
    refine ⟨-z + x.1 ⬝ᵥ x.2, ?_⟩
    rw [Prod.fst_neg, Prod.snd_neg, ← qMat_inv]
    exact H.inv_mem hz

theorem mem_eAddSubgroup_iff {t : ℕ} [NeZero t] (ht : 2 ≤ t) {K : Type*} [Field K]
    (H : Subgroup (SpecialLinearGroup (Fin t) K)) (x : (Mid t → K) × (Mid t → K)) :
    x ∈ eAddSubgroup ht H ↔ ∃ z : K, qMat ht x.1 x.2 z ∈ H :=
  Iff.rfl

theorem isotropic_eAddSubgroup {t : ℕ} [NeZero t] (ht : 2 ≤ t) {K : Type*} [Field K]
    (H : Subgroup (SpecialLinearGroup (Fin t) K))
    {x y : (Mid t → K) × (Mid t → K)} (hx : x ∈ eAddSubgroup ht H)
    (hy : y ∈ eAddSubgroup ht H) :
    x.1 ⬝ᵥ y.2 - y.1 ⬝ᵥ x.2 ∈ zAddSubgroup ht H := by
  obtain ⟨z₁, hz₁⟩ := hx
  obtain ⟨z₂, hz₂⟩ := hy
  have hconj : qMat ht x.1 x.2 z₁ * qMat ht y.1 y.2 z₂ * (qMat ht x.1 x.2 z₁)⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem hz₁ hz₂) (H.inv_mem hz₁)
  rw [qMat_conj] at hconj
  have hmul : (qMat ht y.1 y.2 z₂)⁻¹ *
      qMat ht y.1 y.2 (z₂ + (x.1 ⬝ᵥ y.2 - y.1 ⬝ᵥ x.2)) ∈ H :=
    H.mul_mem (H.inv_mem hz₂) hconj
  rw [qMat_inv, qMat_mul] at hmul
  have heq : qMat ht (-y.1 + y.1) (-y.2 + y.2)
      (-z₂ + y.1 ⬝ᵥ y.2 + (z₂ + (x.1 ⬝ᵥ y.2 - y.1 ⬝ᵥ x.2)) + -y.1 ⬝ᵥ y.2) =
      qMat ht 0 0 (x.1 ⬝ᵥ y.2 - y.1 ⬝ᵥ x.2) := by
    congr 1
    · exact neg_add_cancel y.1
    · exact neg_add_cancel y.2
    · rw [neg_dotProduct]; ring
  rw [heq] at hmul
  exact hmul

theorem card_inf_qSubgroup_eq {t : ℕ} [NeZero t] (ht : 2 ≤ t) {K : Type*} [Field K] [Finite K]
    (H : Subgroup (SpecialLinearGroup (Fin t) K)) :
    Nat.card ↥(H ⊓ qSubgroup ht K) =
      Nat.card (zAddSubgroup ht H) * Nat.card (eAddSubgroup ht H) := by
  let Hq := H.subgroupOf (qSubgroup ht K)
  let π : Hq →* Multiplicative (eAddSubgroup ht H) :=
    { toFun := fun g => Multiplicative.ofAdd ⟨((qSubgroupEquiv ht K).symm g.1).1, by
        obtain ⟨⟨⟨u, v⟩, z⟩, hg⟩ := (qSubgroupEquiv ht K).surjective g.1
        rw [← hg, Equiv.symm_apply_apply]
        exact ⟨z, by
          have hval : g.1.1 = qMat ht u v z := congrArg Subtype.val hg.symm
          rw [← hval]
          exact g.2⟩⟩
      map_one' := by
        have h1 : (1 : qSubgroup ht K) = qSubgroupEquiv ht K ((0, 0), 0) :=
          Subtype.ext (qMat_zero ht).symm
        apply Subtype.ext
        change ((qSubgroupEquiv ht K).symm (1 : qSubgroup ht K)).1 = 0
        rw [h1, Equiv.symm_apply_apply]
        rfl
      map_mul' := fun g₁ g₂ => by
        obtain ⟨⟨⟨u₁, v₁⟩, z₁⟩, hg₁⟩ := (qSubgroupEquiv ht K).surjective g₁.1
        obtain ⟨⟨⟨u₂, v₂⟩, z₂⟩, hg₂⟩ := (qSubgroupEquiv ht K).surjective g₂.1
        have hmul : g₁.1 * g₂.1 =
            qSubgroupEquiv ht K ((u₁ + u₂, v₁ + v₂), z₁ + z₂ + u₁ ⬝ᵥ v₂) := by
          rw [← hg₁, ← hg₂]
          exact Subtype.ext (qMat_mul ht u₁ v₁ u₂ v₂ z₁ z₂)
        apply Subtype.ext
        change ((qSubgroupEquiv ht K).symm (g₁.1 * g₂.1)).1 =
          ((qSubgroupEquiv ht K).symm g₁.1).1 + ((qSubgroupEquiv ht K).symm g₂.1).1
        rw [hmul, ← hg₁, ← hg₂, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
          Equiv.symm_apply_apply]
        rfl }
  have hπ_surj : Function.Surjective π := by
    intro x
    obtain ⟨z, hz⟩ := (Multiplicative.toAdd x).2
    refine ⟨⟨qSubgroupEquiv ht K ((Multiplicative.toAdd x).1, z), hz⟩, ?_⟩
    apply Subtype.ext
    change ((qSubgroupEquiv ht K).symm (qSubgroupEquiv ht K ((Multiplicative.toAdd x).1, z))).1 =
      (Multiplicative.toAdd x).1
    rw [Equiv.symm_apply_apply]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  have h2 : Nat.card (Hq ⧸ π.ker) = Nat.card (Multiplicative (eAddSubgroup ht H)) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ_surj).toEquiv
  have h3 : Nat.card (Multiplicative (eAddSubgroup ht H)) = Nat.card (eAddSubgroup ht H) :=
    Nat.card_congr Multiplicative.toAdd
  have eKer : π.ker ≃ zAddSubgroup ht H :=
    { toFun := fun k => ⟨((qSubgroupEquiv ht K).symm k.1.1).2, by
        have hfst : ((qSubgroupEquiv ht K).symm k.1.1).1 = 0 :=
          congrArg Subtype.val (Multiplicative.ofAdd.injective k.2)
        have hpair : (qSubgroupEquiv ht K).symm k.1.1 =
            ((0, 0), ((qSubgroupEquiv ht K).symm k.1.1).2) :=
          Prod.ext hfst rfl
        have hk_eq := (qSubgroupEquiv ht K).apply_symm_apply k.1.1
        rw [hpair] at hk_eq
        have hval : k.1.1.1 = qMat ht 0 0 ((qSubgroupEquiv ht K).symm k.1.1).2 :=
          congrArg Subtype.val hk_eq.symm
        change qMat ht 0 0 _ ∈ H
        rw [← hval]
        exact k.1.2⟩
      invFun := fun z => ⟨⟨qSubgroupEquiv ht K ((0, 0), z.1), z.2⟩, by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        change ((qSubgroupEquiv ht K).symm (qSubgroupEquiv ht K ((0, 0), z.1))).1 = 0
        rw [Equiv.symm_apply_apply]
        rfl⟩
      left_inv := fun k => by
        have hfst : ((qSubgroupEquiv ht K).symm k.1.1).1 = 0 :=
          congrArg Subtype.val (Multiplicative.ofAdd.injective k.2)
        have hpair : (qSubgroupEquiv ht K).symm k.1.1 =
            ((0, 0), ((qSubgroupEquiv ht K).symm k.1.1).2) :=
          Prod.ext hfst rfl
        have hk_eq := (qSubgroupEquiv ht K).apply_symm_apply k.1.1
        rw [hpair] at hk_eq
        apply Subtype.ext
        apply Subtype.ext
        change qSubgroupEquiv ht K ((0, 0), ((qSubgroupEquiv ht K).symm k.1.1).2) = k.1.1
        exact hk_eq
      right_inv := fun z => by
        apply Subtype.ext
        change ((qSubgroupEquiv ht K).symm (qSubgroupEquiv ht K ((0, 0), z.1))).2 = z.1
        rw [Equiv.symm_apply_apply] }
  rw [← card_subgroupOf, h1, h2, h3, Nat.card_congr eKer, mul_comm]

/-- Any `W₀`-isotropic additive subgroup `E ≤ (M → K) × (M → K)` with `W₀ ≠ ⊤` has
`Nat.card E ≤ Nat.card (M → K)`. -/
theorem card_isotropic_addSubgroup_le {K M : Type*} [Field K] [Finite K] [Fintype M]
    [DecidableEq M] {p : ℕ} [Fact p.Prime] [CharP K p]
    {W₀ : AddSubgroup K} (hW₀ : W₀ ≠ ⊤)
    {E : AddSubgroup ((M → K) × (M → K))}
    (hiso : ∀ x ∈ E, ∀ y ∈ E, x.1 ⬝ᵥ y.2 - y.1 ⬝ᵥ x.2 ∈ W₀) :
    Nat.card E ≤ Nat.card (M → K) := by
  let _ : Algebra (ZMod p) K := ZMod.algebra K p
  have hsmul_K : ∀ (c : ZMod p) (a : K), c • a = algebraMap (ZMod p) K c * a :=
    Algebra.smul_def
  have hsmul_dot_left : ∀ (c : ZMod p) (u v : M → K), (c • u) ⬝ᵥ v = c • (u ⬝ᵥ v) := by
    intro c u v
    simp only [dotProduct, Pi.smul_apply, hsmul_K, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hsmul_dot_right : ∀ (c : ZMod p) (u v : M → K), u ⬝ᵥ (c • v) = c • (u ⬝ᵥ v) := by
    intro c u v
    simp only [dotProduct, Pi.smul_apply, hsmul_K, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  let W₀' : Submodule (ZMod p) K := AddSubgroup.toZModSubmodule p W₀
  have hx₀ : ∃ x₀ : K, x₀ ∉ W₀' := by
    by_contra! hall
    apply hW₀
    rw [eq_top_iff]
    intro x _
    exact hall x
  obtain ⟨x₀, hx₀⟩ := hx₀
  obtain ⟨φ, hφx₀, hφ_ker⟩ := Submodule.exists_le_ker_of_notMem hx₀
  let V := (M → K) × (M → K)
  let E' : Submodule (ZMod p) V := AddSubgroup.toZModSubmodule p E
  let pairMap (x : V) : V →ₗ[ZMod p] ZMod p :=
    { toFun := fun y => φ (x.1 ⬝ᵥ y.2 - y.1 ⬝ᵥ x.2)
      map_add' := fun y₁ y₂ => by
        rw [← map_add]
        congr 1
        change x.1 ⬝ᵥ (y₁.2 + y₂.2) - (y₁.1 + y₂.1) ⬝ᵥ x.2 =
          (x.1 ⬝ᵥ y₁.2 - y₁.1 ⬝ᵥ x.2) + (x.1 ⬝ᵥ y₂.2 - y₂.1 ⬝ᵥ x.2)
        rw [dotProduct_add, add_dotProduct]
        ring
      map_smul' := fun c y => by
        change φ (x.1 ⬝ᵥ (c • y.2) - (c • y.1) ⬝ᵥ x.2) = c • φ (x.1 ⬝ᵥ y.2 - y.1 ⬝ᵥ x.2)
        rw [hsmul_dot_right, hsmul_dot_left, ← smul_sub, map_smul] }
  have hpair_ker : ∀ e : E', E' ≤ LinearMap.ker (pairMap e.1) := by
    intro e y hy
    rw [LinearMap.mem_ker]
    exact hφ_ker (hiso e.1 e.2 y hy)
  let Ψ : E' → Module.Dual (ZMod p) (V ⧸ E') := fun e =>
    Submodule.liftQ E' (pairMap e.1) (hpair_ker e)
  have hΨ_inj : Function.Injective Ψ := by
    intro e₁ e₂ h
    have hdiff : ∀ y : V, φ ((e₁.1.1 - e₂.1.1) ⬝ᵥ y.2 - y.1 ⬝ᵥ (e₁.1.2 - e₂.1.2)) = 0 := by
      intro y
      have hy : Ψ e₁ (Submodule.Quotient.mk y) = Ψ e₂ (Submodule.Quotient.mk y) :=
        congrFun (congrArg DFunLike.coe h) (Submodule.Quotient.mk y)
      have hy' : φ (e₁.1.1 ⬝ᵥ y.2 - y.1 ⬝ᵥ e₁.1.2) = φ (e₂.1.1 ⬝ᵥ y.2 - y.1 ⬝ᵥ e₂.1.2) := hy
      rw [← sub_eq_zero, ← map_sub] at hy'
      rw [← hy']
      congr 1
      simp only [sub_dotProduct, dotProduct_sub]
      ring
    apply Subtype.ext
    apply Prod.ext
    · funext m
      by_contra hm
      set a := (e₁.1.1 - e₂.1.1) m
      have ha : a ≠ 0 := sub_ne_zero.mpr hm
      have h1 := hdiff (0, Pi.single m (a⁻¹ * x₀))
      simp only [dotProduct_single, zero_dotProduct, sub_zero] at h1
      change φ (a * (a⁻¹ * x₀)) = 0 at h1
      rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul] at h1
      exact hφx₀ h1
    · funext m
      by_contra hm
      set b := (e₁.1.2 - e₂.1.2) m
      have hb : b ≠ 0 := sub_ne_zero.mpr hm
      have h1 := hdiff (Pi.single m (-(x₀ * b⁻¹)), 0)
      simp only [dotProduct_zero, single_dotProduct, zero_sub] at h1
      change φ (-(-(x₀ * b⁻¹) * b)) = 0 at h1
      rw [neg_mul, neg_neg, mul_assoc, inv_mul_cancel₀ hb, mul_one] at h1
      exact hφx₀ h1
  have : Finite (V ⧸ E') := inferInstanceAs (Finite (V ⧸ E))
  have : Module.Finite (ZMod p) (V ⧸ E') := Module.Finite.of_finite
  have hcard_dual : Nat.card (Module.Dual (ZMod p) (V ⧸ E')) = Nat.card (V ⧸ E') := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := Module.Dual (ZMod p) (V ⧸ E')),
      Module.natCard_eq_pow_finrank (K := ZMod p) (V := V ⧸ E'), Subspace.dual_finrank_eq]
  have : Finite (Module.Dual (ZMod p) (V ⧸ E')) :=
    Nat.finite_of_card_ne_zero (by rw [hcard_dual]; exact Nat.card_pos.ne')
  have hE_le : Nat.card E ≤ Nat.card (V ⧸ E') := by
    rw [← hcard_dual]
    exact Nat.card_le_card_of_injective Ψ hΨ_inj
  have hquot : Nat.card (V ⧸ E') = Nat.card (V ⧸ E) := rfl
  have hmul : Nat.card E * Nat.card E ≤ Nat.card (M → K) * Nat.card (M → K) := by
    calc Nat.card E * Nat.card E
      _ ≤ Nat.card (V ⧸ E) * Nat.card E := Nat.mul_le_mul_right _ (hquot ▸ hE_le)
      _ = Nat.card V := (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup E).symm
      _ = Nat.card (M → K) * Nat.card (M → K) := Nat.card_prod _ _
  exact Nat.mul_self_le_mul_self_iff.mp hmul

/-- For `t ≥ 3` and `H ≤ SL(t, K)` with `¬ (zSubgroup ht K ≤ H)`,
`Nat.card (eAddSubgroup ht H) ≤ Nat.card K ^ (t - 2)`. -/
theorem card_eAddSubgroup_le {t : ℕ} [NeZero t] (ht : 2 ≤ t) {K : Type*} [Field K] [Finite K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    {H : Subgroup (SpecialLinearGroup (Fin t) K)}
    (hZ : ¬ (zSubgroup ht K ≤ H)) :
    Nat.card (eAddSubgroup ht H) ≤ Nat.card K ^ (t - 2) := by
  have hW₀ : zAddSubgroup ht H ≠ ⊤ := by
    intro htop
    apply hZ
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ zAddSubgroup ht H := htop ▸ AddSubgroup.mem_top z
    exact hz
  rw [← card_mid_fun ht K]
  exact card_isotropic_addSubgroup_le hW₀ (fun x hx y hy => isotropic_eAddSubgroup ht H hx hy)

/-- When `Nat.card K = p` is prime and `¬ (zSubgroup ht K ≤ H)`, `zAddSubgroup ht H = ⊥` and
`Nat.card ↥(H ⊓ qSubgroup ht K) = Nat.card (eAddSubgroup ht H) ≤ p ^ (t - 2)`, so
`p ^ (t - 1) ≤ H.relIndex (qSubgroup ht K)`. -/
theorem prime_field_qSubgroup_bounds {t : ℕ} [NeZero t] (ht : 2 ≤ t) {K : Type*} [Field K]
    [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hK : Nat.card K = p)
    {H : Subgroup (SpecialLinearGroup (Fin t) K)} (hZ : ¬ (zSubgroup ht K ≤ H)) :
    zAddSubgroup ht H = ⊥ ∧
      Nat.card ↥(H ⊓ qSubgroup ht K) = Nat.card (eAddSubgroup ht H) ∧
      Nat.card (eAddSubgroup ht H) ≤ p ^ (t - 2) ∧
      p ^ (t - 1) ≤ H.relIndex (qSubgroup ht K) ∧
      H.relIndex (qSubgroup ht K) ∣ p ^ (2 * t - 3) := by
  have hp : p.Prime := Fact.out
  have hW₀_ne_top : zAddSubgroup ht H ≠ ⊤ := by
    intro htop
    apply hZ
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ zAddSubgroup ht H := htop ▸ AddSubgroup.mem_top z
    exact hz
  have hW₀_bot : zAddSubgroup ht H = ⊥ := by
    by_contra hne_bot
    have hp_le := char_le_card_addSubgroup_of_ne_bot p (zAddSubgroup ht H) hne_bot
    have hR := card_mulStabilizerAddSubgroup_mul_le (zAddSubgroup ht H) hW₀_ne_top
    have hR2 : 2 ≤ Nat.card (mulStabilizerAddSubgroup (zAddSubgroup ht H)) := by
      let f : Bool → mulStabilizerAddSubgroup (zAddSubgroup ht H) := fun b =>
        if b then ⟨1, one_mem_mulStabilizerAddSubgroup _⟩
        else ⟨0, (mulStabilizerAddSubgroup _).zero_mem⟩
      have hf : Function.Injective f := by
        intro b₁ b₂ h
        cases b₁ <;> cases b₂ <;> simp [f] at h ⊢
      have hcard := Nat.card_le_card_of_injective f hf
      have hbool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card]; rfl
      omega
    have hp_pos : 0 < p := hp.pos
    nlinarith
  have hW₀_card : Nat.card (zAddSubgroup ht H) = 1 := by
    rw [hW₀_bot, AddSubgroup.card_bot]
  have hinf_card : Nat.card ↥(H ⊓ qSubgroup ht K) = Nat.card (eAddSubgroup ht H) := by
    rw [card_inf_qSubgroup_eq ht H, hW₀_card, one_mul]
  have hE_le : Nat.card (eAddSubgroup ht H) ≤ p ^ (t - 2) := by
    rw [← hK]
    exact card_eAddSubgroup_le ht hZ
  have hmul : Nat.card ↥(H ⊓ qSubgroup ht K) * H.relIndex (qSubgroup ht K) =
      p ^ (2 * t - 3) := by
    rw [← card_subgroupOf, Subgroup.relIndex, Subgroup.card_mul_index, card_qSubgroup, hK]
  have hdvd : H.relIndex (qSubgroup ht K) ∣ p ^ (2 * t - 3) :=
    ⟨Nat.card ↥(H ⊓ qSubgroup ht K), by rw [← hmul, mul_comm]⟩
  have hrel_ge : p ^ (t - 1) ≤ H.relIndex (qSubgroup ht K) := by
    have hprod : p ^ (t - 2) * p ^ (t - 1) ≤ p ^ (t - 2) * H.relIndex (qSubgroup ht K) := by
      calc p ^ (t - 2) * p ^ (t - 1)
        _ = p ^ ((t - 2) + (t - 1)) := (pow_add p _ _).symm
        _ = p ^ (2 * t - 3) := by congr 1; omega
        _ = Nat.card (eAddSubgroup ht H) * H.relIndex (qSubgroup ht K) := by
            rw [← hinf_card, hmul]
        _ ≤ p ^ (t - 2) * H.relIndex (qSubgroup ht K) := Nat.mul_le_mul_right _ hE_le
    exact le_of_mul_le_mul_left hprod (pow_pos hp.pos _)
  exact ⟨hW₀_bot, hinf_card, hE_le, hrel_ge, hdvd⟩

/-- For `t ≥ 3` and `H ≤ SL(t, K)` with `¬ (zSubgroup _ K ≤ H)`,
`Nat.card K ^ (t - 1) ≤ H.relIndex (qdSubgroup ht K) ≤ H.index`. -/
theorem card_pow_pred_le_relIndex_qdSubgroup {t : ℕ} [NeZero t] (ht : 3 ≤ t)
    {K : Type*} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {H : Subgroup (SpecialLinearGroup (Fin t) K)}
    (hZ : ¬ (zSubgroup (by omega : 2 ≤ t) K ≤ H)) :
    Nat.card K ^ (t - 1) ≤ H.relIndex (qdSubgroup ht K) ∧
      H.relIndex (qdSubgroup ht K) ≤ H.index := by
  have ht2 : 2 ≤ t := by omega
  let Hqd := H.subgroupOf (qdSubgroup ht K)
  let A₀ : Subgroup Kˣ := Hqd.map (qdDiagHom ht K)
  let π := (qdDiagHom ht K).subgroupMap Hqd
  have hπ_surj : Function.Surjective π := (qdDiagHom ht K).subgroupMap_surjective Hqd
  have eKer : π.ker ≃ ↥(H ⊓ qSubgroup ht2 K) :=
    { toFun := fun k => ⟨k.1.1.1, k.1.2, by
        have ha : ((qdSubgroupEquiv ht K).symm k.1.1).2 = 1 :=
          congrArg Subtype.val k.2
        have hpair : (qdSubgroupEquiv ht K).symm k.1.1 =
            (((qdSubgroupEquiv ht K).symm k.1.1).1, 1) :=
          Prod.ext rfl ha
        have hk_eq := (qdSubgroupEquiv ht K).apply_symm_apply k.1.1
        rw [hpair] at hk_eq
        have hval : k.1.1.1 = (((qdSubgroupEquiv ht K).symm k.1.1).1 :
            SpecialLinearGroup (Fin t) K) := by
          have hval' : k.1.1.1 = (((qdSubgroupEquiv ht K).symm k.1.1).1 :
              SpecialLinearGroup (Fin t) K) * dMat ht 1 :=
            congrArg Subtype.val hk_eq.symm
          rw [dMat_one, mul_one] at hval'
          exact hval'
        rw [hval]
        exact ((qdSubgroupEquiv ht K).symm k.1.1).1.2⟩
      invFun := fun q => ⟨⟨qdSubgroupEquiv ht K (⟨q.1, q.2.2⟩, 1), by
        have hmem : q.1 * dMat ht 1 ∈ H := by
          rw [dMat_one, mul_one]
          exact q.2.1
        exact hmem⟩, by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        change ((qdSubgroupEquiv ht K).symm (qdSubgroupEquiv ht K (⟨q.1, q.2.2⟩, 1))).2 = 1
        rw [Equiv.symm_apply_apply]⟩
      left_inv := fun k => by
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        change k.1.1.1 * dMat ht 1 = k.1.1.1
        rw [dMat_one, mul_one]
      right_inv := fun q => by
        apply Subtype.ext
        change q.1 * dMat ht 1 = q.1
        rw [dMat_one, mul_one] }
  have hcard_Hqd : Nat.card Hqd = Nat.card ↥(H ⊓ qSubgroup ht2 K) * Nat.card A₀ := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    have h2 : Nat.card (Hqd ⧸ π.ker) = Nat.card A₀ :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ_surj).toEquiv
    rw [h1, h2, Nat.card_congr eKer, mul_comm]
  let W₀ := zAddSubgroup ht2 H
  have hW₀_ne_top : W₀ ≠ ⊤ := by
    intro htop
    apply hZ
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ W₀ := htop ▸ AddSubgroup.mem_top z
    exact hz
  let R := mulStabilizerAddSubgroup W₀
  let Rnz := {r : R // r.1 ≠ 0}
  have hcard_Rnz : Nat.card Rnz + 1 = Nat.card R := by
    classical
    have eR : R ≃ Option Rnz :=
      { toFun := fun r => if h : r.1 = 0 then none else some ⟨r, h⟩
        invFun := fun o => o.elim 0 Subtype.val
        left_inv := fun r => by
          by_cases h : r.1 = 0
          · simp [h]; exact Subtype.ext h.symm
          · simp [h]
        right_inv := fun o => by
          rcases o with _ | ⟨r, hr⟩
          · simp
          · simp [hr] }
    rw [Nat.card_congr eR, natCard_option]
  have ha_mem : ∀ a : A₀, (a.1 : K) ∈ R ∧ (a.1 : K) ≠ 0 := by
    rintro ⟨a, ⟨g, hgH, ha_g⟩⟩
    refine ⟨fun w hw => ?_, a.ne_zero⟩
    obtain ⟨⟨⟨_, u₀, v₀, z₀, rfl⟩, a'⟩, rfl⟩ := (qdSubgroupEquiv ht K).surjective g
    have ha_eq : a = a' := by
      rw [← ha_g]
      exact congrArg Prod.snd ((qdSubgroupEquiv ht K).symm_apply_apply _)
    subst ha_eq
    have hgH' : qMat ht2 u₀ v₀ z₀ * dMat ht a ∈ H := hgH
    change qMat ht2 0 0 ((a : K) * w) ∈ H
    rw [← qMat_dMat_conj_z ht u₀ v₀ z₀ a w]
    exact H.mul_mem (H.mul_mem hgH' hw) (H.inv_mem hgH')
  let aMap : A₀ → Rnz := fun a => ⟨⟨(a.1 : K), (ha_mem a).1⟩, (ha_mem a).2⟩
  have haMap_inj : Function.Injective aMap := fun a₁ a₂ h =>
    Subtype.ext (Units.ext (congrArg Subtype.val (congrArg Subtype.val h)))
  have hA₀_le : Nat.card A₀ ≤ Nat.card Rnz := Nat.card_le_card_of_injective aMap haMap_inj
  have hW₀_pos : 1 ≤ Nat.card W₀ := Nat.card_pos
  have hWA_le : Nat.card W₀ * Nat.card A₀ ≤ Nat.card K - 1 := by
    have hmul : Nat.card W₀ * Nat.card A₀ + Nat.card W₀ ≤ Nat.card K := by
      calc Nat.card W₀ * Nat.card A₀ + Nat.card W₀
        _ ≤ Nat.card W₀ * Nat.card Rnz + Nat.card W₀ :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ hA₀_le) _
        _ = (Nat.card Rnz + 1) * Nat.card W₀ := by ring
        _ = Nat.card R * Nat.card W₀ := by rw [hcard_Rnz]
        _ ≤ Nat.card K := card_mulStabilizerAddSubgroup_mul_le W₀ hW₀_ne_top
    omega
  have hE_le : Nat.card (eAddSubgroup ht2 H) ≤ Nat.card K ^ (t - 2) :=
    card_eAddSubgroup_le ht2 hZ
  have hHqd_le : Nat.card Hqd ≤ (Nat.card K - 1) * Nat.card K ^ (t - 2) := by
    rw [hcard_Hqd, card_inf_qSubgroup_eq ht2 H]
    calc (Nat.card W₀ * Nat.card (eAddSubgroup ht2 H)) * Nat.card A₀
      _ = (Nat.card W₀ * Nat.card A₀) * Nat.card (eAddSubgroup ht2 H) := by ring
      _ ≤ (Nat.card K - 1) * Nat.card K ^ (t - 2) := Nat.mul_le_mul hWA_le hE_le
  have hmul : Nat.card Hqd * H.relIndex (qdSubgroup ht K) =
      Nat.card K ^ (2 * t - 3) * (Nat.card K - 1) := by
    rw [Subgroup.relIndex, Subgroup.card_mul_index, card_qdSubgroup]
  have hK_gt : 1 < Nat.card K := Finite.one_lt_card
  have hpos : 0 < (Nat.card K - 1) * Nat.card K ^ (t - 2) :=
    Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have hprod : ((Nat.card K - 1) * Nat.card K ^ (t - 2)) * Nat.card K ^ (t - 1) ≤
      ((Nat.card K - 1) * Nat.card K ^ (t - 2)) * H.relIndex (qdSubgroup ht K) := by
    calc ((Nat.card K - 1) * Nat.card K ^ (t - 2)) * Nat.card K ^ (t - 1)
      _ = (Nat.card K ^ (t - 2) * Nat.card K ^ (t - 1)) * (Nat.card K - 1) := by ring
      _ = Nat.card K ^ ((t - 2) + (t - 1)) * (Nat.card K - 1) := by rw [← pow_add]
      _ = Nat.card K ^ (2 * t - 3) * (Nat.card K - 1) := by congr 2; omega
      _ = Nat.card Hqd * H.relIndex (qdSubgroup ht K) := hmul.symm
      _ ≤ ((Nat.card K - 1) * Nat.card K ^ (t - 2)) * H.relIndex (qdSubgroup ht K) :=
          Nat.mul_le_mul_right _ hHqd_le
  exact ⟨le_of_mul_le_mul_left hprod hpos, relIndex_le_index H (qdSubgroup ht K)⟩

/-- The image of `zSubgroup ht K` in `projectiveSL t K` is nontrivial for `t ≥ 2`. -/
theorem map_proj_zSubgroup_ne_bot {t : ℕ} [NeZero t] (ht : 2 ≤ t) (K : Type*) [Field K] :
    (zSubgroup ht K).map (proj t K) ≠ ⊥ := by
  intro hbot
  have hmem : proj t K (qMat ht 0 0 1) ∈ (zSubgroup ht K).map (proj t K) :=
    Subgroup.mem_map_of_mem _ ⟨1, rfl⟩
  rw [hbot, Subgroup.mem_bot, proj_eq_one_iff] at hmem
  obtain ⟨c, -, hc⟩ := hmem
  have hentry := congrFun (congrFun hc (firstIdx t)) (lastIdx t)
  rw [qMat_apply_firstIdx_lastIdx ht, scalar_apply,
    diagonal_apply_ne _ (firstIdx_ne_lastIdx ht)] at hentry
  exact one_ne_zero hentry

/-- For `t ≥ 3` and any proper subgroup `H < projectiveSL t K`, there exists `g : projectiveSL t K`
such that `H₁ := (H.map (MulAut.conj g)).comap (proj t K)` satisfies `H₁.index = H.index` and
`¬ (zSubgroup _ K ≤ H₁)`. -/
theorem exists_comap_not_le_zSubgroup {t : ℕ} [NeZero t] (ht : 3 ≤ t) {K : Type*} [Field K]
    {H : Subgroup (projectiveSL t K)} (hH : H ≠ ⊤) :
    ∃ g : projectiveSL t K,
      let H₁ := (H.map (MulAut.conj g : projectiveSL t K →* projectiveSL t K)).comap (proj t K)
      H₁.index = H.index ∧ ¬ (zSubgroup (by omega : 2 ≤ t) K ≤ H₁) := by
  have _ : IsSimpleGroup (projectiveSL t K) := isSimpleGroup_projectiveSL ht K
  obtain ⟨g, hg⟩ := exists_not_le_map_conj_of_ne_bot hH
    (map_proj_zSubgroup_ne_bot (by omega : 2 ≤ t) K)
  refine ⟨g, ?_, ?_⟩
  · rw [Subgroup.index_comap_of_surjective _ (proj_surjective t K),
      Subgroup.index_map_equiv H (MulAut.conj g)]
  · rw [← Subgroup.map_le_iff_le_comap]
    exact hg

/-- For `t ≥ 3` and any proper subgroup `H < projectiveSL t K` (`H ≠ ⊤`),
`Nat.card K ^ (t - 1) ≤ H.index`. -/
theorem card_pow_pred_le_index_of_ne_top {t : ℕ} (ht : 3 ≤ t) {K : Type*} [Field K] [Finite K]
    {H : Subgroup (projectiveSL t K)} (hH : H ≠ ⊤) :
    Nat.card K ^ (t - 1) ≤ H.index := by
  have _ : NeZero t := ⟨by omega⟩
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : p.Prime := CharP.char_is_prime K p
  have _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hidx, hZ⟩ := exists_comap_not_le_zSubgroup ht hH
  obtain ⟨hle1, hle2⟩ := card_pow_pred_le_relIndex_qdSubgroup ht hZ
  exact hidx ▸ le_trans hle1 hle2

/-- For `t ≥ 3` and any primitive action of `G` on `α` with socle `T ≃* projectiveSL t K`,
`Nat.card K ^ (t - 1) ≤ Nat.card α`. -/
theorem card_pow_pred_le_card_of_three_le {α : Type*} {K : Type} [Finite α] [Field K] [Finite K]
    {T : Subgroup (Perm α)} [MulAction.IsPretransitive T α]
    {t : ℕ} (ht : 3 ≤ t) (e : T ≃* projectiveSL t K) :
    Nat.card K ^ (t - 1) ≤ Nat.card α := by
  have _ : NeZero t := ⟨by omega⟩
  obtain ⟨x, hx⟩ := exists_not_le_ptStab_of_ne_bot e
    (map_proj_zSubgroup_ne_bot (by omega : 2 ≤ t) K)
  rw [← index_ptStab_eq_card e x]
  apply card_pow_pred_le_index_of_ne_top ht
  intro htop
  exact hx (htop ▸ le_top)

/-- Order of `projectiveSL 3 K` when `Nat.card K = 3` is `5616`. -/
theorem card_projectiveSL_three_three {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 3) :
    Nat.card (projectiveSL 3 K) = 5616 := by
  have h1 := (scalars 3 K).card_eq_card_quotient_mul_card_subgroup
  have hSL : Nat.card (SpecialLinearGroup (Fin 3) K) = 5616 := by
    rw [card_SL_eq (by omega : 1 ≤ 3), hK]
    decide
  have hsc_bot : scalars 3 K = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨c, hc3, hg⟩
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [hg]
    have hc2 : c ^ 2 = 1 := by
      have hcard_units : Nat.card Kˣ = 2 := by rw [Nat.card_units, hK]
      rw [← hcard_units]
      exact pow_card_eq_one'
    have hc1 : c = 1 := by
      calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
        _ = 1 := by rw [hc3, hc2, inv_one, mul_one]
    rw [hc1, Units.val_one, map_one]
    rfl
  have hsc : Nat.card (scalars 3 K) = 1 := by
    rw [hsc_bot, Subgroup.card_bot]
  rw [hSL, hsc, mul_one] at h1
  exact h1.symm

/-- For `t = 3` and `Nat.card K = 3`, every proper subgroup `H < projectiveSL 3 K` has
`13 ≤ H.index`. -/
theorem thirteen_le_index_of_three_three {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 3)
    {H : Subgroup (projectiveSL 3 K)} (hH : H ≠ ⊤) :
    13 ≤ H.index := by
  have _ : IsSimpleGroup (projectiveSL 3 K) := isSimpleGroup_projectiveSL le_rfl K
  have hdvd := card_dvd_index_factorial_of_ne_top hH
  rw [card_projectiveSL_three_three hK] at hdvd
  have h13 : 13 ∣ (H.index).factorial := dvd_trans (by decide : 13 ∣ 5616) hdvd
  exact (by decide : Nat.Prime 13).dvd_factorial.mp h13

/-- For `t = 3` and `Nat.card K = 3`, `13 ≤ Nat.card α`. -/
theorem thirteen_le_card_of_three_three {α : Type*} {K : Type} [Finite α] [Field K] [Finite K]
    {T : Subgroup (Perm α)} (e : T ≃* projectiveSL 3 K) (hK : Nat.card K = 3) :
    13 ≤ Nat.card α := by
  have hdvd : 13 ∣ Nat.card (projectiveSL 3 K) := by
    rw [card_projectiveSL_three_three hK]
    decide
  exact prime_le_card_of_faithfulSMul (G := T) (α := α) (by decide : Nat.Prime 13)
    ((Nat.card_congr e.toEquiv).symm ▸ hdvd)

/-- When `Nat.card K = 2`, `scalars t K = ⊥`. -/
theorem scalars_eq_bot_of_card_two (t : ℕ) {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    scalars t K = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨c, -, hg⟩
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hg]
  have hc1 : c = 1 := by
    have hcard_units : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
    have := pow_card_eq_one' (x := c)
    rwa [hcard_units, pow_one] at this
  rw [hc1, Units.val_one, map_one]
  rfl

/-- Order of `projectiveSL 3 K` when `Nat.card K = 2` is `168`. -/
theorem card_projectiveSL_three_two {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card (projectiveSL 3 K) = 168 := by
  have h1 := (scalars 3 K).card_eq_card_quotient_mul_card_subgroup
  have hSL : Nat.card (SpecialLinearGroup (Fin 3) K) = 168 := by
    rw [card_SL_eq (by omega : 1 ≤ 3), hK]
    decide
  have hsc : Nat.card (scalars 3 K) = 1 := by
    rw [scalars_eq_bot_of_card_two 3 hK, Subgroup.card_bot]
  rw [hSL, hsc, mul_one] at h1
  exact h1.symm

/-- For `t = 3` and `Nat.card K = 2`, every proper subgroup `H < projectiveSL 3 K` has
`7 ≤ H.index`. -/
theorem seven_le_index_of_three_two {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2)
    {H : Subgroup (projectiveSL 3 K)} (hH : H ≠ ⊤) :
    7 ≤ H.index := by
  have _ : IsSimpleGroup (projectiveSL 3 K) := isSimpleGroup_projectiveSL le_rfl K
  have hdvd := card_dvd_index_factorial_of_ne_top hH
  rw [card_projectiveSL_three_two hK] at hdvd
  have h7 : 7 ∣ (H.index).factorial := dvd_trans (by decide : 7 ∣ 168) hdvd
  exact Nat.prime_seven.dvd_factorial.mp h7

/-- For `t = 3` and `Nat.card K = 2`, every proper subgroup `H < SL(3, K)` has `7 ≤ H.index`. -/
theorem seven_le_index_sl_three_two {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2)
    {H : Subgroup (SpecialLinearGroup (Fin 3) K)} (hH : H ≠ ⊤) :
    7 ≤ H.index := by
  have hker : (proj 3 K).ker = ⊥ := by
    rw [ker_proj, scalars_eq_bot_of_card_two 3 hK]
  have hinj : Function.Injective (proj 3 K) := (MonoidHom.ker_eq_bot_iff (proj 3 K)).mp hker
  let e : SpecialLinearGroup (Fin 3) K ≃* projectiveSL 3 K :=
    MulEquiv.ofBijective (proj 3 K) ⟨hinj, proj_surjective 3 K⟩
  have hmap_ne : H.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hH
    rw [eq_top_iff]
    intro g _
    have hg : e g ∈ H.map e.toMonoidHom := htop ▸ Subgroup.mem_top (e g)
    obtain ⟨h, hhH, hhe⟩ := hg
    exact hinj hhe ▸ hhH
  rw [← Subgroup.index_map_equiv H e]
  exact seven_le_index_of_three_two hK hmap_ne

end Maroti
