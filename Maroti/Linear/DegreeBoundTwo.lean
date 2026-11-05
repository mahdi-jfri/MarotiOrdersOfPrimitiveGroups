module

public import Maroti.Linear.ActionBasics
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

/-!
# Minimal degree bounds for `PSL(2, q)`

This file establishes the permutation degree lower bounds for primitive actions of almost simple
groups with socle `S ≅ PSL(2, p^f)` (`p` prime, `f ≥ 2`):

* The theorem `Maroti.card_mulStabilizerAddSubgroup_mul_le` proves the multiplier ring bound for a
  proper additive subgroup `W₀` of a finite field `K`: if `R = {r ∈ K | ∀ w ∈ W₀, r * w ∈ W₀}`,
  then `|R| * |W₀| ≤ |K|`.
* The theorem `Maroti.exists_borel_index_two` uses the Borel subgroup `upperTriangular 2 K` of
  `SL(2, K)` to find a point `x : α` whose stabilizer `Hb` in `upperTriangular 2 K` has
  `Hb.index ≤ Nat.card α`, `Nat.card Hb * Hb.index = q * (q - 1)`, `Nat.card Hb ≤ q - 1` when
  `p = 2`, and `Nat.card Hb ≤ 2 * (q - p)` when `p ≥ 3`.
* Dedicated theorems prove the degree lower bounds for the small fields `q ∈ {8, 9, 25, 27}` where
  the raw Borel bound `(q+1)/2` is below the threshold needed in `Maroti/Linear/NumericBound.lean`.
-/

public section

namespace Maroti

open Subgroup Equiv Matrix
open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem natCard_option (α : Type*) [Finite α] : Nat.card (Option α) = Nat.card α + 1 := by
  have := Fintype.ofFinite α
  simp [Nat.card_eq_fintype_card]

theorem card_subgroupOf {G : Type*} [Group G] (A B : Subgroup G) :
    Nat.card ↥(A.subgroupOf B) = Nat.card ↥(A ⊓ B) := by
  rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective B.subtype_injective]

/-- The multiplier ring of an additive subgroup `W₀ : AddSubgroup K` in a field `K`: the additive
subgroup of elements `r : K` such that `r * w ∈ W₀` for all `w ∈ W₀`. -/
@[expose]
def mulStabilizerAddSubgroup {K : Type*} [Field K] (W₀ : AddSubgroup K) : AddSubgroup K where
  carrier := {r : K | ∀ w ∈ W₀, r * w ∈ W₀}
  zero_mem' := fun w _ => by
    rw [zero_mul]
    exact W₀.zero_mem
  add_mem' := fun {r₁ r₂} hr₁ hr₂ w hw => by
    rw [add_mul]
    exact W₀.add_mem (hr₁ w hw) (hr₂ w hw)
  neg_mem' := fun {r} hr w hw => by
    rw [neg_mul]
    exact W₀.neg_mem (hr w hw)

theorem one_mem_mulStabilizerAddSubgroup {K : Type*} [Field K] (W₀ : AddSubgroup K) :
    (1 : K) ∈ mulStabilizerAddSubgroup W₀ := fun w hw => by
  rw [one_mul]
  exact hw

/-- If `W₀` is a proper additive subgroup of a finite field `K`, then
`Nat.card (mulStabilizerAddSubgroup W₀) * Nat.card W₀ ≤ Nat.card K`. -/
theorem card_mulStabilizerAddSubgroup_mul_le {K : Type*} [Field K] [Finite K]
    (W₀ : AddSubgroup K) (hW₀ : W₀ ≠ ⊤) :
    Nat.card (mulStabilizerAddSubgroup W₀) * Nat.card W₀ ≤ Nat.card K := by
  have hx₀ : ∃ x₀ : K, x₀ ∉ W₀ := by
    by_contra! h
    apply hW₀
    rw [eq_top_iff]
    intro x _
    exact h x
  obtain ⟨x₀, hx₀⟩ := hx₀
  let R := mulStabilizerAddSubgroup W₀
  let φ : R →+ K ⧸ W₀ :=
    { toFun := fun r => QuotientAddGroup.mk (r.1 * x₀)
      map_zero' := by
        change QuotientAddGroup.mk ((0 : K) * x₀) = 0
        rw [zero_mul, QuotientAddGroup.mk_zero]
      map_add' := fun r₁ r₂ => by
        change QuotientAddGroup.mk ((r₁.1 + r₂.1) * x₀) =
          QuotientAddGroup.mk (r₁.1 * x₀) + QuotientAddGroup.mk (r₂.1 * x₀)
        rw [add_mul, QuotientAddGroup.mk_add] }
  have hφ_inj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    have hmem : r.1 * x₀ ∈ W₀ := (QuotientAddGroup.eq_zero_iff (r.1 * x₀)).mp hr
    apply Subtype.ext
    by_contra hr0
    let μ : W₀ → W₀ := fun w => ⟨r.1 * w.1, r.2 w.1 w.2⟩
    have hμ_inj : Function.Injective μ := by
      intro w₁ w₂ hw
      exact Subtype.ext (mul_left_cancel₀ hr0 (congrArg Subtype.val hw))
    have hμ_surj : Function.Surjective μ := Finite.surjective_of_injective hμ_inj
    obtain ⟨⟨w, hw⟩, hwx₀⟩ := hμ_surj ⟨r.1 * x₀, hmem⟩
    have heq : w = x₀ := mul_left_cancel₀ hr0 (congrArg Subtype.val hwx₀)
    exact hx₀ (heq ▸ hw)
  have hle : Nat.card R ≤ Nat.card (K ⧸ W₀) := Nat.card_le_card_of_injective φ hφ_inj
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup W₀]
  exact Nat.mul_le_mul_right _ hle

/-- Upper unitriangular matrix `[[1, w], [0, 1]]` in `SL(2, K)`. -/
@[expose]
def uMat2 {K : Type*} [Field K] (w : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, w; 0, 1], by simp⟩

/-- Diagonal matrix `[[a, 0], [0, a⁻¹]]` in `SL(2, K)`. -/
@[expose]
def dMat2 {K : Type*} [Field K] (a : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)], by simp⟩

@[simp]
theorem coe_uMat2 {K : Type*} [Field K] (w : K) :
    (uMat2 w : Matrix (Fin 2) (Fin 2) K) = !![1, w; 0, 1] :=
  rfl

@[simp]
theorem coe_dMat2 {K : Type*} [Field K] (a : Kˣ) :
    (dMat2 a : Matrix (Fin 2) (Fin 2) K) = !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] :=
  rfl

theorem sl2_ext {K : Type*} [Field K] {A B : SpecialLinearGroup (Fin 2) K}
    (h : (A : Matrix (Fin 2) (Fin 2) K) = (B : Matrix (Fin 2) (Fin 2) K)) : A = B :=
  Subtype.ext h

theorem uMat2_mem_unitriangular {K : Type*} [Field K] (w : K) :
    uMat2 w ∈ unitriangular 2 K := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [uMat2] at hij ⊢
  · fin_cases i <;> rfl

theorem uMat2_mem_upperTriangular {K : Type*} [Field K] (w : K) :
    uMat2 w ∈ upperTriangular 2 K :=
  (uMat2_mem_unitriangular w).1

theorem dMat2_mem_upperTriangular {K : Type*} [Field K] (a : Kˣ) :
    dMat2 a ∈ upperTriangular 2 K := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [dMat2] at hij ⊢

theorem uMat2_zero {K : Type*} [Field K] : uMat2 (0 : K) = 1 := by
  apply sl2_ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem uMat2_mul {K : Type*} [Field K] (w₁ w₂ : K) :
    uMat2 w₁ * uMat2 w₂ = uMat2 (w₁ + w₂) := by
  apply Subtype.ext
  change (!![1, w₁; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![1, w₂; 0, 1] = !![1, w₁ + w₂; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

theorem uMat2_inv {K : Type*} [Field K] (w : K) :
    (uMat2 w)⁻¹ = uMat2 (-w) := by
  rw [inv_eq_iff_mul_eq_one, uMat2_mul, add_neg_cancel, uMat2_zero]

theorem uMat2_injective {K : Type*} [Field K] : Function.Injective (uMat2 : K → _) := by
  intro w₁ w₂ h
  have := congrFun (congrFun (congrArg Subtype.val h) 0) 1
  simpa [uMat2] using this

theorem unitriangular2_eq_uMat2 {K : Type*} [Field K] {A : SpecialLinearGroup (Fin 2) K}
    (hA : A ∈ unitriangular 2 K) :
    A = uMat2 ((A : Matrix (Fin 2) (Fin 2) K) 0 1) := by
  apply sl2_ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact hA.2 0
  · rfl
  · exact hA.1 1 0 (by decide)
  · exact hA.2 1

theorem dMat2_one {K : Type*} [Field K] : dMat2 (1 : Kˣ) = 1 := by
  apply sl2_ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem dMat2_mul {K : Type*} [Field K] (a b : Kˣ) :
    dMat2 a * dMat2 b = dMat2 (a * b) := by
  apply Subtype.ext
  change (!![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K) *
      !![(b : K), 0; 0, ((b⁻¹ : Kˣ) : K)] =
    !![((a * b : Kˣ) : K), 0; 0, (((a * b)⁻¹ : Kˣ) : K)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [_root_.mul_inv_rev, mul_comm]

theorem uMat2_dMat2_mul_uMat2 {K : Type*} [Field K] (w₀ : K) (a : Kˣ) (w : K) :
    (uMat2 w₀ * dMat2 a) * uMat2 w = uMat2 ((a : K) ^ 2 * w) * (uMat2 w₀ * dMat2 a) := by
  apply Subtype.ext
  change ((!![1, w₀; 0, 1] : Matrix (Fin 2) (Fin 2) K) *
      !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)]) * !![1, w; 0, 1] =
    !![1, (a : K) ^ 2 * w; 0, 1] *
      (!![1, w₀; 0, 1] * !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)])
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  calc (a : K) * w + w₀ * (a : K)⁻¹
    _ = w₀ * (a : K)⁻¹ + (a : K) * w * ((a : K) * (a : K)⁻¹) := by
        rw [mul_inv_cancel₀ a.ne_zero]; ring
    _ = w₀ * (a : K)⁻¹ + (a : K) ^ 2 * w * (a : K)⁻¹ := by ring

theorem conj_uMat2 {K : Type*} [Field K] (w₀ : K) (a : Kˣ) (w : K) :
    (uMat2 w₀ * dMat2 a) * uMat2 w * (uMat2 w₀ * dMat2 a)⁻¹ = uMat2 ((a : K) ^ 2 * w) := by
  rw [mul_inv_eq_iff_eq_mul, uMat2_dMat2_mul_uMat2]

theorem uMat2_dMat2_mul {K : Type*} [Field K] (w₁ : K) (a₁ : Kˣ) (w₂ : K) (a₂ : Kˣ) :
    (uMat2 w₁ * dMat2 a₁) * (uMat2 w₂ * dMat2 a₂) =
      uMat2 (w₁ + (a₁ : K) ^ 2 * w₂) * dMat2 (a₁ * a₂) := by
  calc (uMat2 w₁ * dMat2 a₁) * (uMat2 w₂ * dMat2 a₂)
    _ = ((uMat2 w₁ * dMat2 a₁) * uMat2 w₂) * dMat2 a₂ := by group
    _ = (uMat2 ((a₁ : K) ^ 2 * w₂) * (uMat2 w₁ * dMat2 a₁)) * dMat2 a₂ := by
        rw [uMat2_dMat2_mul_uMat2]
    _ = (uMat2 ((a₁ : K) ^ 2 * w₂) * uMat2 w₁) * (dMat2 a₁ * dMat2 a₂) := by group
    _ = uMat2 (w₁ + (a₁ : K) ^ 2 * w₂) * dMat2 (a₁ * a₂) := by
        rw [uMat2_mul, add_comm, dMat2_mul]

/-- Explicit equivalence between `K × Kˣ` and `upperTriangular 2 K`. -/
@[expose]
def upperTriangular2Equiv (K : Type*) [Field K] : K × Kˣ ≃ upperTriangular 2 K where
  toFun p := ⟨uMat2 p.1 * dMat2 p.2,
    (upperTriangular 2 K).mul_mem (uMat2_mem_upperTriangular p.1) (dMat2_mem_upperTriangular p.2)⟩
  invFun B :=
    have h10 : (B.1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := B.2 1 0 (by decide)
    have hdet :
        (B.1 : Matrix (Fin 2) (Fin 2) K) 0 0 * (B.1 : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
      have h := B.1.2
      rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at h
      exact h
    have hdet' : (B.1 : Matrix (Fin 2) (Fin 2) K) 1 1 * (B.1 : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 :=
      mul_comm ((B.1 : Matrix (Fin 2) (Fin 2) K) 1 1) ((B.1 : Matrix (Fin 2) (Fin 2) K) 0 0) ▸ hdet
    ((B.1 : Matrix (Fin 2) (Fin 2) K) 0 1 * (B.1 : Matrix (Fin 2) (Fin 2) K) 0 0,
      ⟨(B.1 : Matrix (Fin 2) (Fin 2) K) 0 0, (B.1 : Matrix (Fin 2) (Fin 2) K) 1 1, hdet, hdet'⟩)
  left_inv p := by
    obtain ⟨w, a⟩ := p
    ext
    · change ((!![1, w; 0, 1] : Matrix (Fin 2) (Fin 2) K) *
          !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)]) 0 1 *
        ((!![1, w; 0, 1] : Matrix (Fin 2) (Fin 2) K) *
          !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)]) 0 0 = w
      simp
    · change ((!![1, w; 0, 1] : Matrix (Fin 2) (Fin 2) K) *
          !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)]) 0 0 = (a : K)
      simp
  right_inv B := by
    have h10 : (B.1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := B.2 1 0 (by decide)
    have hdet :
        (B.1 : Matrix (Fin 2) (Fin 2) K) 0 0 * (B.1 : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
      have h := B.1.2
      rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at h
      exact h
    apply Subtype.ext
    apply Subtype.ext
    change (!![1, (B.1 : Matrix (Fin 2) (Fin 2) K) 0 1 *
        (B.1 : Matrix (Fin 2) (Fin 2) K) 0 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) *
      !![(B.1 : Matrix (Fin 2) (Fin 2) K) 0 0, 0;
        0, (B.1 : Matrix (Fin 2) (Fin 2) K) 1 1] = (B.1 : Matrix (Fin 2) (Fin 2) K)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10]
    rw [mul_assoc, hdet, mul_one]

theorem card_upperTriangular_two {K : Type*} [Field K] [Finite K] :
    Nat.card (upperTriangular 2 K) = Nat.card K * (Nat.card K - 1) := by
  rw [← Nat.card_congr (upperTriangular2Equiv K), Nat.card_prod, Nat.card_units]

theorem card_SL_two {K : Type*} [Field K] [Finite K] :
    Nat.card (SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  rw [card_SL_eq (by omega : 1 ≤ 2), show 2 * (2 - 1) / 2 = 1 from rfl, pow_one,
    Finset.Icc_self, Finset.prod_singleton]

theorem card_projectiveSL_two_mul_scalars {K : Type*} [Field K] [Finite K] :
    Nat.card (projectiveSL 2 K) * Nat.card (scalars 2 K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  have h := (scalars 2 K).card_eq_card_quotient_mul_card_subgroup
  rw [card_SL_two] at h
  exact h.symm

theorem card_projUpperTriangular_two_mul_scalars {K : Type*} [Field K] [Finite K] :
    Nat.card (projUpperTriangular 2 K) * Nat.card (scalars 2 K) =
      Nat.card K * (Nat.card K - 1) := by
  let π : upperTriangular 2 K →* projUpperTriangular 2 K :=
    (proj 2 K).subgroupMap (upperTriangular 2 K)
  have hπ_surj : Function.Surjective π := (proj 2 K).subgroupMap_surjective _
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  have h2 : Nat.card (upperTriangular 2 K ⧸ π.ker) = Nat.card (projUpperTriangular 2 K) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ_surj).toEquiv
  have hker : π.ker = (scalars 2 K).subgroupOf (upperTriangular 2 K) := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subtype.ext_iff]
    exact proj_eq_one_iff
  have h3 : Nat.card π.ker = Nat.card (scalars 2 K) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (scalars_le_upperTriangular 2 K)).toEquiv
  rw [card_upperTriangular_two, h2, h3] at h1
  exact h1.symm

/-- Projection to the `Kˣ` component of `upperTriangular 2 K`. -/
@[expose]
def upperTriangular2DiagHom (K : Type*) [Field K] : upperTriangular 2 K →* Kˣ where
  toFun B := ((upperTriangular2Equiv K).symm B).2
  map_one' := by
    have h1 : (1 : upperTriangular 2 K) = upperTriangular2Equiv K (0, 1) := by
      apply Subtype.ext
      change (1 : SpecialLinearGroup (Fin 2) K) = uMat2 0 * dMat2 1
      rw [uMat2_zero, dMat2_one, one_mul]
    rw [h1, Equiv.symm_apply_apply]
  map_mul' B₁ B₂ := by
    obtain ⟨⟨w₁, a₁⟩, rfl⟩ := (upperTriangular2Equiv K).surjective B₁
    obtain ⟨⟨w₂, a₂⟩, rfl⟩ := (upperTriangular2Equiv K).surjective B₂
    have hmul : upperTriangular2Equiv K (w₁, a₁) * upperTriangular2Equiv K (w₂, a₂) =
        upperTriangular2Equiv K (w₁ + (a₁ : K) ^ 2 * w₂, a₁ * a₂) := by
      apply Subtype.ext
      exact uMat2_dMat2_mul w₁ a₁ w₂ a₂
    rw [hmul, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- If `g ∈ SL(2, K)` conjugates `uMat2 w` (`w ≠ 0`) to `uMat2 w'` in `projectiveSL 2 K`, then
`g ∈ upperTriangular 2 K`. -/
theorem mem_upperTriangular_of_proj_conj_uMat2 {K : Type*} [Field K]
    {g : SpecialLinearGroup (Fin 2) K} {w w' : K} (hw : w ≠ 0)
    (hconj : proj 2 K g * proj 2 K (uMat2 w) * (proj 2 K g)⁻¹ = proj 2 K (uMat2 w')) :
    g ∈ upperTriangular 2 K := by
  have heq : proj 2 K (uMat2 w' * g) = proj 2 K (g * uMat2 w) := by
    rw [map_mul, map_mul, ← hconj, mul_assoc, inv_mul_cancel, mul_one]
  obtain ⟨c, -, hc⟩ := proj_eq_proj_iff.mp heq
  set G : Matrix (Fin 2) (Fin 2) K := (g : Matrix (Fin 2) (Fin 2) K)
  have hmat : G * !![1, w; 0, 1] = (!![1, w'; 0, 1] * G) * scalar (Fin 2) (c : K) := by
    have hmul : (uMat2 w' * g) * ((uMat2 w' * g)⁻¹ * (g * uMat2 w)) = g * uMat2 w :=
      mul_inv_cancel_left (uMat2 w' * g) (g * uMat2 w)
    have hval : (!![1, w'; 0, 1] * G) *
        (((uMat2 w' * g)⁻¹ * (g * uMat2 w) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) = G * !![1, w; 0, 1] :=
      congrArg Subtype.val hmul
    rw [← hval, hc]
  have h10 := congrFun (congrFun hmat 1) 0
  have h11 := congrFun (congrFun hmat 1) 1
  simp [scalar_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h10 h11
  have hsq : G 1 0 * G 1 0 * w = 0 := by
    linear_combination G 1 0 * h11 - G 1 1 * h10
  have hg10 : G 1 0 = 0 := by
    rcases mul_eq_zero.mp hsq with h0 | hw0
    · exact mul_self_eq_zero.mp h0
    · exact absurd hw0 hw
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  exact hg10

/-- Every nontrivial subgroup `P ≤ projUnitriangular 2 K` has normalizer in `projectiveSL 2 K`
contained in `projUpperTriangular 2 K`. -/
theorem normalizer_le_projUpperTriangular_of_le_projUnitriangular {K : Type*} [Field K]
    {P : Subgroup (projectiveSL 2 K)} (hPU : P ≤ projUnitriangular 2 K) (hP : P ≠ ⊥) :
    Subgroup.normalizer (P : Set (projectiveSL 2 K)) ≤ projUpperTriangular 2 K := by
  have hex : ∃ p ∈ P, p ≠ 1 := by
    by_contra! hall
    apply hP
    rw [eq_bot_iff]
    intro p hp
    exact Subgroup.mem_bot.mpr (hall p hp)
  obtain ⟨p, hpP, hp1⟩ := hex
  obtain ⟨A, hAU, rfl⟩ := hPU hpP
  have hA_eq := unitriangular2_eq_uMat2 hAU
  set w := (A : Matrix (Fin 2) (Fin 2) K) 0 1
  have hw : w ≠ 0 := by
    intro hw0
    apply hp1
    rw [hA_eq, hw0, uMat2_zero, map_one]
  intro s hs
  obtain ⟨g, rfl⟩ := proj_surjective 2 K s
  have hconj_mem : proj 2 K g * proj 2 K (uMat2 w) * (proj 2 K g)⁻¹ ∈ P := by
    rw [← hA_eq]
    exact (Subgroup.mem_normalizer_iff.mp hs (proj 2 K A)).mp hpP
  obtain ⟨B, hBU, hB_eq⟩ := hPU hconj_mem
  rw [unitriangular2_eq_uMat2 hBU] at hB_eq
  exact ⟨g, mem_upperTriangular_of_proj_conj_uMat2 hw hB_eq.symm, rfl⟩

/-- Every additive subgroup `W₀` of a field `K` of prime characteristic `p` with `W₀ ≠ ⊥` has
`p ≤ Nat.card W₀`. -/
theorem char_le_card_addSubgroup_of_ne_bot {K : Type*} [Field K] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] (W₀ : AddSubgroup K) (hW₀ : W₀ ≠ ⊥) :
    p ≤ Nat.card W₀ := by
  have hex : ∃ w ∈ W₀, w ≠ 0 := by
    by_contra! hall
    apply hW₀
    rw [eq_bot_iff]
    intro w hw
    exact AddSubgroup.mem_bot.mpr (hall w hw)
  obtain ⟨w₁, hw₁, hw₁0⟩ := hex
  let ψ : ZMod p → W₀ := fun c => ⟨(c.val : K) * w₁, by
    simpa [nsmul_eq_mul] using W₀.nsmul_mem hw₁ c.val⟩
  have hψ_inj : Function.Injective ψ := by
    intro c₁ c₂ hc
    have hmul : ((c₁.val : K) - (c₂.val : K)) * w₁ = 0 := by
      have := congrArg Subtype.val hc
      change (c₁.val : K) * w₁ = (c₂.val : K) * w₁ at this
      linear_combination this
    have hsub : (c₁.val : K) = (c₂.val : K) :=
      sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hw₁0)
    have hmod : c₁.val % p = c₂.val % p :=
      (CharP.natCast_eq_natCast K p).mp hsub
    exact ZMod.val_injective p
      ((Nat.mod_eq_of_lt c₁.val_lt).symm.trans (Eq.trans hmod (Nat.mod_eq_of_lt c₂.val_lt)))
  have hcard : Nat.card (ZMod p) ≤ Nat.card W₀ := Nat.card_le_card_of_injective ψ hψ_inj
  rwa [Nat.card_zmod] at hcard

/-- Additive subgroup of `K` corresponding to the unitriangular part of
`Hb ≤ upperTriangular 2 K`. -/
@[expose]
def unitriangularAddSubgroup {K : Type*} [Field K] (Hb : Subgroup (upperTriangular 2 K)) :
    AddSubgroup K where
  carrier := {w : K | (⟨uMat2 w, uMat2_mem_upperTriangular w⟩ : upperTriangular 2 K) ∈ Hb}
  zero_mem' := by
    change (⟨uMat2 0, _⟩ : upperTriangular 2 K) ∈ Hb
    have : (⟨uMat2 0, uMat2_mem_upperTriangular 0⟩ : upperTriangular 2 K) = 1 :=
      Subtype.ext uMat2_zero
    rw [this]
    exact Hb.one_mem
  add_mem' := fun {w₁ w₂} hw₁ hw₂ => by
    change (⟨uMat2 (w₁ + w₂), _⟩ : upperTriangular 2 K) ∈ Hb
    have : (⟨uMat2 (w₁ + w₂), uMat2_mem_upperTriangular (w₁ + w₂)⟩ : upperTriangular 2 K) =
        ⟨uMat2 w₁, uMat2_mem_upperTriangular w₁⟩ *
          ⟨uMat2 w₂, uMat2_mem_upperTriangular w₂⟩ :=
      Subtype.ext (uMat2_mul w₁ w₂).symm
    rw [this]
    exact Hb.mul_mem hw₁ hw₂
  neg_mem' := fun {w} hw => by
    change (⟨uMat2 (-w), _⟩ : upperTriangular 2 K) ∈ Hb
    have : (⟨uMat2 (-w), uMat2_mem_upperTriangular (-w)⟩ : upperTriangular 2 K) =
        (⟨uMat2 w, uMat2_mem_upperTriangular w⟩)⁻¹ :=
      Subtype.ext (uMat2_inv w).symm
    rw [this]
    exact Hb.inv_mem hw

/-- Decomposition and order bound for a subgroup `Hb ≤ upperTriangular 2 K` in terms of its
unitriangular intersection `W₀` and diagonal projection `A₀`. -/
theorem card_sub_upperTriangular_two_bounds {K : Type*} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) [CharP K p] (Hb : Subgroup (upperTriangular 2 K))
    (hU_not_le : ¬ ∀ w : K, (⟨uMat2 w, uMat2_mem_upperTriangular w⟩ : upperTriangular 2 K) ∈ Hb) :
    let W₀ := unitriangularAddSubgroup Hb
    let A₀ : Subgroup Kˣ := Hb.map (upperTriangular2DiagHom K)
    Nat.card Hb = Nat.card W₀ * Nat.card A₀ ∧
      Nat.card W₀ ∣ Nat.card K ∧
      Nat.card A₀ ∣ Nat.card K - 1 ∧
      (p = 2 → Nat.card Hb ≤ Nat.card K - 1) ∧
      (3 ≤ p → Nat.card W₀ = 1 → Nat.card Hb ≤ Nat.card K - 1) ∧
      (3 ≤ p → W₀ ≠ ⊥ → Nat.card Hb ≤ 2 * (Nat.card K - p)) := by
  intro W₀ A₀
  have : Fact p.Prime := ⟨hp⟩
  have hW₀_ne_top : W₀ ≠ ⊤ := by
    intro htop
    apply hU_not_le
    intro w
    have hw : w ∈ W₀ := htop.symm ▸ AddSubgroup.mem_top w
    exact hw
  let π : Hb →* A₀ := (upperTriangular2DiagHom K).subgroupMap Hb
  have hπ_surj : Function.Surjective π := (upperTriangular2DiagHom K).subgroupMap_surjective Hb
  have eKer : π.ker ≃ W₀ :=
    { toFun := fun x => ⟨((upperTriangular2Equiv K).symm x.1.1).1, by
        have hdiag : ((upperTriangular2Equiv K).symm x.1.1).2 = 1 :=
          congrArg Subtype.val x.2
        have hx_eq := (upperTriangular2Equiv K).apply_symm_apply x.1.1
        set w := ((upperTriangular2Equiv K).symm x.1.1).1
        have hpair : (upperTriangular2Equiv K).symm x.1.1 = (w, 1) :=
          Prod.ext rfl hdiag
        have h1 : x.1.1 = ⟨uMat2 w, uMat2_mem_upperTriangular w⟩ := by
          rw [← hx_eq, hpair]
          apply Subtype.ext
          change uMat2 w * dMat2 1 = uMat2 w
          rw [dMat2_one, mul_one]
        change (⟨uMat2 w, uMat2_mem_upperTriangular w⟩ : upperTriangular 2 K) ∈ Hb
        rw [← h1]
        exact x.1.2⟩
      invFun := fun w => ⟨⟨⟨uMat2 w.1, uMat2_mem_upperTriangular w.1⟩, w.2⟩, by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        have heq : (⟨uMat2 w.1, uMat2_mem_upperTriangular w.1⟩ : upperTriangular 2 K) =
            upperTriangular2Equiv K (w.1, 1) := by
          apply Subtype.ext
          change uMat2 w.1 = uMat2 w.1 * dMat2 1
          rw [dMat2_one, mul_one]
        change ((upperTriangular2Equiv K).symm
          ⟨uMat2 w.1, uMat2_mem_upperTriangular w.1⟩).2 = 1
        rw [heq, Equiv.symm_apply_apply]⟩
      left_inv := fun x => by
        have hdiag : ((upperTriangular2Equiv K).symm x.1.1).2 = 1 :=
          congrArg Subtype.val x.2
        have hx_eq := (upperTriangular2Equiv K).apply_symm_apply x.1.1
        set w := ((upperTriangular2Equiv K).symm x.1.1).1
        have hpair : (upperTriangular2Equiv K).symm x.1.1 = (w, 1) :=
          Prod.ext rfl hdiag
        apply Subtype.ext
        apply Subtype.ext
        rw [← hx_eq, hpair]
        apply Subtype.ext
        change uMat2 w = uMat2 w * dMat2 1
        rw [dMat2_one, mul_one]
      right_inv := fun w => by
        apply Subtype.ext
        have heq : (⟨uMat2 w.1, uMat2_mem_upperTriangular w.1⟩ : upperTriangular 2 K) =
            upperTriangular2Equiv K (w.1, 1) := by
          apply Subtype.ext
          change uMat2 w.1 = uMat2 w.1 * dMat2 1
          rw [dMat2_one, mul_one]
        change ((upperTriangular2Equiv K).symm
          ⟨uMat2 w.1, uMat2_mem_upperTriangular w.1⟩).1 = w.1
        rw [heq, Equiv.symm_apply_apply] }
  have hcard_H : Nat.card Hb = Nat.card W₀ * Nat.card A₀ := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    have h2 : Nat.card (Hb ⧸ π.ker) = Nat.card A₀ :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ_surj).toEquiv
    rw [h1, h2, Nat.card_congr eKer, mul_comm]
  have hW₀_dvd : Nat.card W₀ ∣ Nat.card K :=
    AddSubgroup.card_addSubgroup_dvd_card W₀
  have hA₀_dvd : Nat.card A₀ ∣ Nat.card K - 1 := by
    rw [← Nat.card_units]
    exact Subgroup.card_subgroup_dvd_card A₀
  let R := mulStabilizerAddSubgroup W₀
  have hR_bound : Nat.card R * Nat.card W₀ ≤ Nat.card K :=
    card_mulStabilizerAddSubgroup_mul_le W₀ hW₀_ne_top
  have hsq_mem : ∀ a : A₀, (a.1 : K) ^ 2 ∈ R ∧ (a.1 : K) ^ 2 ≠ 0 := by
    rintro ⟨a, ⟨B, hB, ha_B⟩⟩
    refine ⟨fun w hw => ?_, pow_ne_zero 2 (Units.ne_zero a)⟩
    obtain ⟨⟨w₀, a'⟩, hB_eq⟩ := (upperTriangular2Equiv K).surjective B
    have ha_eq : a = a' := by
      rw [← ha_B, ← hB_eq]
      exact congrArg Prod.snd ((upperTriangular2Equiv K).symm_apply_apply (w₀, a'))
    subst ha_eq
    change (⟨uMat2 ((a : K) ^ 2 * w), _⟩ : upperTriangular 2 K) ∈ Hb
    have hconj_eq : (⟨uMat2 ((a : K) ^ 2 * w), uMat2_mem_upperTriangular _⟩ :
        upperTriangular 2 K) =
        B * ⟨uMat2 w, uMat2_mem_upperTriangular w⟩ * B⁻¹ := by
      rw [← hB_eq]
      exact Subtype.ext (conj_uMat2 w₀ a w).symm
    rw [hconj_eq]
    exact Hb.mul_mem (Hb.mul_mem hB hw) (Hb.inv_mem hB)
  let Rnz := {r : R // r.1 ≠ 0}
  have hcard_Rnz : Nat.card Rnz + 1 = Nat.card R := by
    classical
    have eR : R ≃ Option Rnz :=
      { toFun := fun r => if h : r.1 = 0 then none else some ⟨r, h⟩
        invFun := fun o => o.elim 0 Subtype.val
        left_inv := fun r => by
          by_cases h : r.1 = 0
          · simp [h]
            exact Subtype.ext h.symm
          · simp [h]
        right_inv := fun o => by
          rcases o with _ | ⟨r, hr⟩
          · simp
          · simp [hr] }
    rw [Nat.card_congr eR, natCard_option]
  have hW₀_pos : 1 ≤ Nat.card W₀ := Nat.card_pos
  have hp2_bound : p = 2 → Nat.card Hb ≤ Nat.card K - 1 := by
    intro hp2
    subst hp2
    let sqMap : A₀ → Rnz := fun a => ⟨⟨(a.1 : K) ^ 2, (hsq_mem a).1⟩, (hsq_mem a).2⟩
    have hsq_inj : Function.Injective sqMap := by
      intro a₁ a₂ h
      have heq : (a₁.1 : K) ^ 2 = (a₂.1 : K) ^ 2 :=
        congrArg Subtype.val (congrArg Subtype.val h)
      have h20 : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
      have hsub : ((a₁.1 : K) - (a₂.1 : K)) ^ 2 = 0 := by
        calc ((a₁.1 : K) - (a₂.1 : K)) ^ 2
          _ = (a₁.1 : K) ^ 2 + (a₂.1 : K) ^ 2 - 2 * (a₁.1 : K) * (a₂.1 : K) := by ring
          _ = 0 := by
              rw [heq, ← two_mul, h20]
              ring
      exact Subtype.ext (Units.ext (sub_eq_zero.mp (sq_eq_zero_iff.mp hsub)))
    have hA₀_le : Nat.card A₀ ≤ Nat.card Rnz := Nat.card_le_card_of_injective sqMap hsq_inj
    rw [hcard_H]
    have hmul : Nat.card W₀ * Nat.card A₀ + Nat.card W₀ ≤ Nat.card K := by
      calc Nat.card W₀ * Nat.card A₀ + Nat.card W₀
        _ ≤ Nat.card W₀ * Nat.card Rnz + Nat.card W₀ :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ hA₀_le) _
        _ = (Nat.card Rnz + 1) * Nat.card W₀ := by ring
        _ = Nat.card R * Nat.card W₀ := by rw [hcard_Rnz]
        _ ≤ Nat.card K := hR_bound
    omega
  have hp3_triv : 3 ≤ p → Nat.card W₀ = 1 → Nat.card Hb ≤ Nat.card K - 1 := by
    intro _ hW1
    rw [hcard_H, hW1, one_mul]
    exact Nat.le_of_dvd (by have := Finite.one_lt_card (α := K); omega) hA₀_dvd
  have hp3_nontriv : 3 ≤ p → W₀ ≠ ⊥ → Nat.card Hb ≤ 2 * (Nat.card K - p) := by
    intro _ hW_ne
    have hp_le_W₀ : p ≤ Nat.card W₀ := char_le_card_addSubgroup_of_ne_bot p W₀ hW_ne
    have hA₀_le : Nat.card A₀ ≤ 2 * Nat.card Rnz := by
      classical
      let f : A₀ → Rnz := fun a => ⟨⟨(a.1 : K) ^ 2, (hsq_mem a).1⟩, (hsq_mem a).2⟩
      let rep : Rnz → K := fun r =>
        if h : ∃ a : A₀, f a = r then (Classical.choose h).1 else 0
      let g : A₀ → Rnz × Bool := fun a => (f a, decide ((a.1 : K) = rep (f a)))
      have hg_inj : Function.Injective g := by
        intro a₁ a₂ h
        have hf_eq : f a₁ = f a₂ := congrArg Prod.fst h
        have hb_eq : decide ((a₁.1 : K) = rep (f a₁)) = decide ((a₂.1 : K) = rep (f a₂)) :=
          congrArg Prod.snd h
        rw [hf_eq] at hb_eq
        have hex : ∃ a : A₀, f a = f a₂ := ⟨a₂, rfl⟩
        set a₀ := Classical.choose hex
        have ha₀ : f a₀ = f a₂ := Classical.choose_spec hex
        have hrep : rep (f a₂) = (a₀.1 : K) := dite_eq_left hex
        have hsq1 : (a₁.1 : K) ^ 2 = (a₀.1 : K) ^ 2 :=
          congrArg Subtype.val (congrArg Subtype.val (hf_eq.trans ha₀.symm))
        have hsq2 : (a₂.1 : K) ^ 2 = (a₀.1 : K) ^ 2 :=
          congrArg Subtype.val (congrArg Subtype.val ha₀.symm)
        have hpm1 : (a₁.1 : K) = (a₀.1 : K) ∨ (a₁.1 : K) = -(a₀.1 : K) :=
          sq_eq_sq_iff_eq_or_eq_neg.mp hsq1
        have hpm2 : (a₂.1 : K) = (a₀.1 : K) ∨ (a₂.1 : K) = -(a₀.1 : K) :=
          sq_eq_sq_iff_eq_or_eq_neg.mp hsq2
        apply Subtype.ext
        apply Units.ext
        by_cases h1 : (a₁.1 : K) = rep (f a₂)
        · have h2 : (a₂.1 : K) = rep (f a₂) := of_decide_eq_true (hb_eq ▸ decide_eq_true h1)
          exact h1.trans h2.symm
        · have h2 : (a₂.1 : K) ≠ rep (f a₂) :=
            of_decide_eq_false (hb_eq ▸ decide_eq_false h1)
          rw [hrep] at h1 h2
          exact (hpm1.resolve_left h1).trans (hpm2.resolve_left h2).symm
      have hbool : Nat.card Bool = 2 := by
        rw [Nat.card_eq_fintype_card]
        rfl
      calc Nat.card A₀ ≤ Nat.card (Rnz × Bool) := Nat.card_le_card_of_injective g hg_inj
        _ = Nat.card Rnz * 2 := by rw [Nat.card_prod, hbool]
        _ = 2 * Nat.card Rnz := mul_comm _ _
    rw [hcard_H]
    have hmul : Nat.card W₀ * Nat.card Rnz + Nat.card W₀ ≤ Nat.card K := by
      calc Nat.card W₀ * Nat.card Rnz + Nat.card W₀
        _ = (Nat.card Rnz + 1) * Nat.card W₀ := by ring
        _ = Nat.card R * Nat.card W₀ := by rw [hcard_Rnz]
        _ ≤ Nat.card K := hR_bound
    calc Nat.card W₀ * Nat.card A₀
      _ ≤ Nat.card W₀ * (2 * Nat.card Rnz) := Nat.mul_le_mul_left _ hA₀_le
      _ = 2 * (Nat.card W₀ * Nat.card Rnz) := by ring
      _ ≤ 2 * (Nat.card K - p) := by omega
  exact ⟨hcard_H, hW₀_dvd, hA₀_dvd, hp2_bound, hp3_triv, hp3_nontriv⟩

/-- Main Borel subgroup index bound for `projectiveSL 2 K` acting on `α`. -/
theorem exists_borel_index_two {α : Type*} {K : Type} [Finite α] [Field K] [Finite K]
    {T : Subgroup (Perm α)} (e : T ≃* projectiveSL 2 K) {p : ℕ} (hp : p.Prime) [CharP K p] :
    ∃ x : α,
      ¬ (projUnitriangular 2 K ≤ ptStab e x) ∧
      (ptStab e x).relIndex (projUpperTriangular 2 K) ≤ Nat.card α ∧
      (ptStab e x).relIndex (projUpperTriangular 2 K) ∣ Nat.card K * (Nat.card K - 1) ∧
      (p = 2 → Nat.card K ≤ (ptStab e x).relIndex (projUpperTriangular 2 K)) ∧
      (3 ≤ p →
        Nat.card K * (Nat.card K - 1) ≤
          2 * (Nat.card K - p) * (ptStab e x).relIndex (projUpperTriangular 2 K) ∨
        Nat.card K ≤ (ptStab e x).relIndex (projUpperTriangular 2 K)) := by
  have hK_gt : 1 < Nat.card K := Finite.one_lt_card
  have hU_ne_bot : projUnitriangular 2 K ≠ ⊥ := by
    intro hbot
    have hcard := card_projUnitriangular (K := K) 2
    rw [hbot, Subgroup.card_bot, show 2 * (2 - 1) / 2 = 1 from rfl, pow_one] at hcard
    omega
  obtain ⟨x, hx⟩ := exists_not_le_ptStab_of_ne_bot e hU_ne_bot
  let π : upperTriangular 2 K →* projUpperTriangular 2 K :=
    (proj 2 K).subgroupMap (upperTriangular 2 K)
  have hπ_surj : Function.Surjective π := (proj 2 K).subgroupMap_surjective _
  let H₀ : Subgroup (projUpperTriangular 2 K) :=
    (ptStab e x).subgroupOf (projUpperTriangular 2 K)
  let Hb : Subgroup (upperTriangular 2 K) := H₀.comap π
  have hindex_eq : Hb.index = (ptStab e x).relIndex (projUpperTriangular 2 K) :=
    Subgroup.index_comap_of_surjective H₀ hπ_surj
  have hU_not_le :
      ¬ ∀ w : K, (⟨uMat2 w, uMat2_mem_upperTriangular w⟩ : upperTriangular 2 K) ∈ Hb := by
    intro hall
    apply hx
    rintro _ ⟨A, hA, rfl⟩
    rw [unitriangular2_eq_uMat2 hA]
    exact hall ((A : Matrix (Fin 2) (Fin 2) K) 0 1)
  obtain ⟨hcard_H, _, _, hp2, hp3_triv, hp3_nontriv⟩ :=
    card_sub_upperTriangular_two_bounds hp Hb hU_not_le
  have hmul : Nat.card Hb * Hb.index = Nat.card K * (Nat.card K - 1) := by
    rw [Subgroup.card_mul_index, card_upperTriangular_two]
  obtain ⟨hrel_le, _, _, _⟩ := relIndex_ptStab_props e (projUpperTriangular 2 K) x
  refine ⟨x, hx, hrel_le, ⟨Nat.card Hb, by rw [← hindex_eq, ← hmul, mul_comm]⟩, ?_, ?_⟩
  · intro hp2_eq
    have hle := hp2 hp2_eq
    rw [← hindex_eq]
    have hpos : 0 < Nat.card K - 1 := by omega
    have hprod : (Nat.card K - 1) * Nat.card K ≤ (Nat.card K - 1) * Hb.index := by
      calc (Nat.card K - 1) * Nat.card K
        _ = Nat.card Hb * Hb.index := by rw [mul_comm, hmul]
        _ ≤ (Nat.card K - 1) * Hb.index := Nat.mul_le_mul_right _ hle
    exact le_of_mul_le_mul_left hprod hpos
  · intro hp3
    rw [← hindex_eq]
    by_cases hW_bot : unitriangularAddSubgroup Hb = ⊥
    · right
      have hW1 : Nat.card (unitriangularAddSubgroup Hb) = 1 := by
        rw [hW_bot, AddSubgroup.card_bot]
      have hle := hp3_triv hp3 hW1
      have hpos : 0 < Nat.card K - 1 := by omega
      have hprod : (Nat.card K - 1) * Nat.card K ≤ (Nat.card K - 1) * Hb.index := by
        calc (Nat.card K - 1) * Nat.card K
          _ = Nat.card Hb * Hb.index := by rw [mul_comm, hmul]
          _ ≤ (Nat.card K - 1) * Hb.index := Nat.mul_le_mul_right _ hle
      exact le_of_mul_le_mul_left hprod hpos
    · left
      have hle := hp3_nontriv hp3 hW_bot
      rw [← hmul]
      exact Nat.mul_le_mul_right _ hle

/-- Corollary of `exists_borel_index_two`: for `p ≥ 3, f ≥ 2`, `(p^f + 1) / 2 ≤ Nat.card α`. -/
theorem half_card_add_one_le_card_of_odd {α : Type*} {K : Type} [Finite α] [Field K] [Finite K]
    {T : Subgroup (Perm α)} (e : T ≃* projectiveSL 2 K) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    [CharP K p] (hq : 9 ≤ Nat.card K) :
    (Nat.card K + 1) / 2 ≤ Nat.card α := by
  obtain ⟨x, _, hrel_le, _, _, hodd⟩ := exists_borel_index_two e hp
  set q := Nat.card K
  set idx := (ptStab e x).relIndex (projUpperTriangular 2 K)
  rcases hodd hp3 with h1 | h2
  · have hqp : q - p < q - 1 := by omega
    have hlt : q * (q - p) < 2 * (q - p) * idx := by
      calc q * (q - p) < q * (q - 1) := Nat.mul_lt_mul_of_pos_left hqp (by omega)
        _ ≤ 2 * (q - p) * idx := h1
    have h2idx : q < 2 * idx := by nlinarith
    omega
  · omega

/-- For `q = 27` (`p = 3, f = 3`), `18 ≤ Nat.card α`. -/
theorem eighteen_le_card_of_twenty_seven {α : Type*} {K : Type} [Finite α] [Field K] [Finite K]
    {T : Subgroup (Perm α)} (e : T ≃* projectiveSL 2 K) [CharP K 3] (hK : Nat.card K = 27) :
    18 ≤ Nat.card α := by
  obtain ⟨x, _, hrel_le, hdvd, _, hodd⟩ := exists_borel_index_two e Nat.prime_three
  rw [hK] at hdvd hodd
  set idx := (ptStab e x).relIndex (projUpperTriangular 2 K)
  rcases hodd le_rfl with h1 | h2
  · have h15 : 15 ≤ idx := by omega
    have h18 : 18 ≤ idx := by
      by_contra! hlt
      revert hdvd
      interval_cases idx <;> decide
    exact le_trans h18 hrel_le
  · omega

/-- If `Nat.card G = p ^ k * m` with `¬ p ∣ m`, then every `P : Sylow p G` has
`Nat.card P = p ^ k` and `(P : Subgroup G).index = m`. -/
theorem card_sylow_and_index_eq {G : Type*} [Group G] [Finite G] {p k m : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hG : Nat.card G = p ^ k * m) (hm : ¬ p ∣ m) :
    Nat.card P = p ^ k ∧ (P : Subgroup G).index = m := by
  have hp : p.Prime := Fact.out
  have hdvd1 : p ^ k ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card ⟨m, hG⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.2
  have hcop : (Nat.card P).Coprime m := by
    rw [hn]
    exact (hp.coprime_iff_not_dvd.mpr hm).pow_left n
  have hdvd2 : Nat.card P ∣ p ^ k := by
    apply hcop.dvd_of_dvd_mul_right
    rw [← hG]
    exact (P : Subgroup G).card_subgroup_dvd_card
  have hcard : Nat.card P = p ^ k := Nat.dvd_antisymm hdvd2 hdvd1
  refine ⟨hcard, ?_⟩
  have hmul := (P : Subgroup G).card_mul_index
  rw [hcard, hG] at hmul
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos k) hmul

/-- In any finite group `H` and prime `p`, if every Sylow `p`-subgroup of `H` has cardinality `p`,
then `Nat.card (Sylow p H) * (p - 1) ≤ Nat.card {h : H // orderOf h = p}`. -/
theorem card_sylow_mul_pred_le_card_orderOf {H : Type*} [Group H] [Finite H] (p : ℕ)
    [Fact p.Prime] (hcard : ∀ Q : Sylow p H, Nat.card Q = p) :
    Nat.card (Sylow p H) * (p - 1) ≤ Nat.card {h : H // orderOf h = p} := by
  classical
  have hp : p.Prime := Fact.out
  let φ : (Σ Q : Sylow p H, {x : Q // x ≠ 1}) → {h : H // orderOf h = p} := fun s =>
    ⟨s.2.1.1, by
      have hdvd : orderOf s.2.1.1 ∣ p := by
        rw [← Subgroup.orderOf_mk]
        exact hcard s.1 ▸ orderOf_dvd_natCard s.2.1
      rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hp_eq
      · exfalso
        exact s.2.2 (Subtype.ext (orderOf_eq_one_iff.mp h1))
      · exact hp_eq⟩
  have hφ_inj : Function.Injective φ := by
    rintro ⟨Q₁, ⟨⟨g, hg₁⟩, hne₁⟩⟩ ⟨Q₂, ⟨⟨g₂, hg₂⟩, hne₂⟩⟩ h
    have hgeq : g = g₂ := congrArg Subtype.val h
    subst hgeq
    have hord : orderOf g = p := (φ ⟨Q₁, ⟨⟨g, hg₁⟩, hne₁⟩⟩).2
    have hQ_eq : Q₁ = Q₂ := by
      apply Sylow.ext
      have h1 : Subgroup.zpowers g = (Q₁ : Subgroup H) :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg₁)
          (by rw [Nat.card_zpowers, hord, hcard Q₁])
      have h2 : Subgroup.zpowers g = (Q₂ : Subgroup H) :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg₂)
          (by rw [Nat.card_zpowers, hord, hcard Q₂])
      exact h1.symm.trans h2
    subst hQ_eq
    rfl
  have hsigma : Nat.card (Σ Q : Sylow p H, {x : Q // x ≠ 1}) =
      Nat.card (Sylow p H) * (p - 1) := by
    have := Fintype.ofFinite (Sylow p H)
    rw [Nat.card_sigma]
    have hconst : ∀ Q : Sylow p H, Nat.card {x : Q // x ≠ 1} = p - 1 := by
      intro Q
      have eQ : Q ≃ Option {x : Q // x ≠ 1} :=
        { toFun := fun x => if h : x = 1 then none else some ⟨x, h⟩
          invFun := fun o => o.elim 1 Subtype.val
          left_inv := fun x => by
            by_cases h : x = 1
            · simp [h]
            · simp [h]
          right_inv := fun o => by
            rcases o with _ | ⟨x, hx⟩
            · simp
            · simp [hx] }
      have := Nat.card_congr eQ
      rw [natCard_option, hcard Q] at this
      omega
    simp [hconst, Nat.card_eq_fintype_card]
  rw [← hsigma]
  exact Nat.card_le_card_of_injective φ hφ_inj

/-- If `Nat.card (Sylow p H) = 1`, then every `P : Sylow p H` is normal in `H`. -/
theorem normal_of_card_sylow_eq_one {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (h1 : Nat.card (Sylow p H) = 1) (P : Sylow p H) :
    (P : Subgroup H).Normal := by
  have : Subsingleton (Sylow p H) := Finite.card_le_one_iff_subsingleton.mp h1.le
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  intro g _
  exact Sylow.smul_eq_iff_mem_normalizer.mp (Subsingleton.elim (g • P) P)

/-- For `q = 25` (`p = 5, f = 2`), `16 ≤ Nat.card α`. -/
theorem sixteen_le_card_of_twenty_five {α : Type*} {K : Type} [Finite α] [Field K] [Finite K]
    {T : Subgroup (Perm α)} [MulAction.IsPretransitive T α]
    (e : T ≃* projectiveSL 2 K) [CharP K 5] (hK : Nat.card K = 25)
    (hS_card : Nat.card (projectiveSL 2 K) = 7800) :
    16 ≤ Nat.card α := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  obtain ⟨x, hx, hrel_le, hdvd, _, hodd⟩ := exists_borel_index_two e Nat.prime_five
  rw [hK] at hdvd hodd
  set H := ptStab e x
  set idx := H.relIndex (projUpperTriangular 2 K)
  have h15_idx : 15 ≤ idx := by
    rcases hodd (by omega) with h1 | h2 <;> omega
  have h15_n : 15 ≤ Nat.card α := le_trans h15_idx hrel_le
  rcases lt_or_eq_of_le h15_n with h16 | hn15
  · exact h16
  exfalso
  have hidx15 : idx = 15 := le_antisymm (hn15.symm ▸ hrel_le) h15_idx
  have hH_card : Nat.card H = 520 := by
    have hmul : Nat.card H * Nat.card α = Nat.card (projectiveSL 2 K) :=
      card_ptStab_mul_card e x
    rw [← hn15, hS_card] at hmul
    omega
  have hB_card : Nat.card (projUpperTriangular 2 K) = 300 := by
    have h1 := card_projectiveSL_two_mul_scalars (K := K)
    have h2 := card_projUpperTriangular_two_mul_scalars (K := K)
    rw [hS_card, hK, show 25 * (25 ^ 2 - 1) = 15600 from rfl] at h1
    rw [hK, show 25 * (25 - 1) = 600 from rfl] at h2
    have hsc2 : Nat.card (scalars 2 K) = 2 := by omega
    rw [hsc2] at h2
    omega
  obtain ⟨_, _, hHB_mul_raw, _⟩ := relIndex_ptStab_props e (projUpperTriangular 2 K) x
  have hHB_mul : Nat.card ↥(projUpperTriangular 2 K ⊓ H) * idx =
      Nat.card (projUpperTriangular 2 K) := hHB_mul_raw
  rw [hidx15, hB_card] at hHB_mul
  have hHB_card : Nat.card ↥(projUpperTriangular 2 K ⊓ H) = 20 := by omega
  obtain ⟨hrel_U, hdvd_U, hHU_mul_raw, _⟩ := relIndex_ptStab_props e (projUnitriangular 2 K) x
  set rU := (ptStab e x).relIndex (projUnitriangular 2 K)
  have hHU_mul : Nat.card ↥(projUnitriangular 2 K ⊓ H) * rU =
      Nat.card (projUnitriangular 2 K) := hHU_mul_raw
  have hU_card : Nat.card (projUnitriangular 2 K) = 25 := by
    rw [card_projUnitriangular, hK]
    rfl
  rw [hU_card] at hdvd_U hHU_mul
  rw [← hn15] at hrel_U
  have hHU_card : Nat.card ↥(projUnitriangular 2 K ⊓ H) = 5 := by
    have hnot25 : ¬ (25 ∣ Nat.card H) := by rw [hH_card]; decide
    have hne25 : Nat.card ↥(projUnitriangular 2 K ⊓ H) ≠ 25 := by
      intro h25
      apply hnot25
      rw [← h25, ← card_subgroupOf]
      exact Subgroup.card_subgroup_dvd_card _
    have hrel_cases : rU = 1 ∨ rU = 5 := by
      have hr_pos : 0 < rU := Nat.pos_of_dvd_of_pos hdvd_U (by omega)
      revert hdvd_U
      interval_cases rU <;> decide
    rcases hrel_cases with hr1 | hr5
    · rw [hr1] at hHU_mul
      omega
    · rw [hr5] at hHU_mul
      omega
  let P₅_sub : Subgroup H := (projUnitriangular 2 K).subgroupOf H
  have hP₅_card : Nat.card P₅_sub = 5 := by
    rw [card_subgroupOf, hHU_card]
  have hP₅_pgroup : IsPGroup 5 P₅_sub := IsPGroup.of_card (n := 1) (by rw [hP₅_card, pow_one])
  let P₅ : Sylow 5 H := hP₅_pgroup.toSylow (by
    have h := P₅_sub.card_mul_index
    rw [hP₅_card, hH_card] at h
    have hidx : P₅_sub.index = 104 := by omega
    rw [hidx]
    decide)
  have hnorm_P₅ : Subgroup.normalizer (P₅_sub : Set H) ≤
      (projUpperTriangular 2 K).subgroupOf H := by
    have hmap_le : Subgroup.normalizer ((projUnitriangular 2 K ⊓ H : Subgroup _) : Set _) ≤
        projUpperTriangular 2 K := by
      apply normalizer_le_projUpperTriangular_of_le_projUnitriangular inf_le_left
      intro hbot
      rw [hbot, Subgroup.card_bot] at hHU_card
      omega
    intro h hh
    rw [Subgroup.mem_subgroupOf]
    apply hmap_le
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · rintro ⟨hsU, hsH⟩
      have hconj := (Subgroup.mem_normalizer_iff.mp hh ⟨s, hsH⟩).mp hsU
      exact ⟨hconj, H.mul_mem (H.mul_mem h.2 hsH) (H.inv_mem h.2)⟩
    · rintro ⟨hsU, hsH⟩
      have hs' : h.1 * s * h.1⁻¹ ∈ H := hsH
      have hsH_orig : s ∈ H := by
        simpa [mul_assoc] using H.mul_mem (H.mul_mem (H.inv_mem h.2) hs') h.2
      have hconj := (Subgroup.mem_normalizer_iff.mp hh ⟨s, hsH_orig⟩).mpr hsU
      exact ⟨hconj, hsH_orig⟩
  have hnorm_card_le : Nat.card (Subgroup.normalizer (P₅_sub : Set H)) ≤ 20 := by
    calc Nat.card (Subgroup.normalizer (P₅_sub : Set H))
      _ ≤ Nat.card ↥((projUpperTriangular 2 K).subgroupOf H) :=
          Subgroup.card_le_of_le hnorm_P₅
      _ = Nat.card ↥(projUpperTriangular 2 K ⊓ H) := card_subgroupOf _ _
      _ = 20 := hHB_card
  have hsylow5_ge : 26 ≤ Nat.card (Sylow 5 H) := by
    have heq : Nat.card (Sylow 5 H) = (Subgroup.normalizer (P₅_sub : Set H)).index :=
      Sylow.card_eq_index_normalizer P₅
    have h := (Subgroup.normalizer (P₅_sub : Set H)).card_mul_index
    rw [hH_card, ← heq] at h
    nlinarith
  have hcard_Q5 : ∀ Q : Sylow 5 H, Nat.card Q = 5 := by
    intro Q
    exact (card_sylow_and_index_eq Q (k := 1) (m := 104) (by omega) (by decide)).1
  have h5_ord := card_sylow_mul_pred_le_card_orderOf (H := H) 5 hcard_Q5
  obtain ⟨P₁₃⟩ : Nonempty (Sylow 13 H) := Sylow.nonempty
  obtain ⟨hP₁₃_card, hP₁₃_idx⟩ :=
    card_sylow_and_index_eq P₁₃ (k := 1) (m := 40) (by omega) (by decide)
  have hcard_Q13 : ∀ Q : Sylow 13 H, Nat.card Q = 13 := by
    intro Q
    exact (card_sylow_and_index_eq Q (k := 1) (m := 40) (by omega) (by decide)).1
  have hn13_dvd : Nat.card (Sylow 13 H) ∣ 40 := hP₁₃_idx ▸ Sylow.card_dvd_index P₁₃
  have hn13_mod : Nat.card (Sylow 13 H) ≡ 1 [MOD 13] := card_sylow_modEq_one 13 H
  have hn13_cases : Nat.card (Sylow 13 H) = 1 ∨ Nat.card (Sylow 13 H) = 40 := by
    set m := Nat.card (Sylow 13 H)
    have hm_pos : 0 < m := Nat.card_pos
    have hm_le : m ≤ 40 := Nat.le_of_dvd (by omega) hn13_dvd
    revert hn13_dvd hn13_mod
    interval_cases m <;> decide
  rcases hn13_cases with hn13_1 | hn13_40
  · have hP₁₃_norm : (P₁₃ : Subgroup H).Normal := normal_of_card_sylow_eq_one hn13_1 P₁₃
    let Q := H ⧸ (P₁₃ : Subgroup H)
    let πQ : H →* Q := QuotientGroup.mk' (P₁₃ : Subgroup H)
    have hπQ_surj : Function.Surjective πQ := QuotientGroup.mk'_surjective _
    have hQ_card : Nat.card Q = 40 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (P₁₃ : Subgroup H)
      rw [hH_card, hP₁₃_card] at h
      change 520 = Nat.card Q * (13 ^ 1) at h
      omega
    obtain ⟨S₅⟩ : Nonempty (Sylow 5 Q) := Sylow.nonempty
    obtain ⟨hS₅_card, hS₅_idx⟩ :=
      card_sylow_and_index_eq S₅ (k := 1) (m := 8) (by omega) (by decide)
    have hn5Q_dvd : Nat.card (Sylow 5 Q) ∣ 8 := hS₅_idx ▸ Sylow.card_dvd_index S₅
    have hn5Q_mod : Nat.card (Sylow 5 Q) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 Q
    have hn5Q_1 : Nat.card (Sylow 5 Q) = 1 := by
      set m := Nat.card (Sylow 5 Q)
      have hm_pos : 0 < m := Nat.card_pos
      have hm_le : m ≤ 8 := Nat.le_of_dvd (by omega) hn5Q_dvd
      revert hn5Q_dvd hn5Q_mod
      interval_cases m <;> decide
    have : Subsingleton (Sylow 5 Q) := Finite.card_le_one_iff_subsingleton.mp hn5Q_1.le
    let L : Subgroup H := (S₅ : Subgroup Q).comap πQ
    have hL_idx : L.index = 8 :=
      (Subgroup.index_comap_of_surjective (S₅ : Subgroup Q) hπQ_surj).trans hS₅_idx
    have hL_card : Nat.card L = 65 := by
      have h := L.card_mul_index
      rw [hL_idx, hH_card] at h
      omega
    let emb : {h : H // orderOf h = 5} → L := fun ⟨h₀, hh₀⟩ =>
      ⟨h₀, by
        have hpow1 : h₀ ^ 5 = 1 := hh₀ ▸ pow_orderOf_eq_one h₀
        let C : Subgroup Q := Subgroup.zpowers (πQ h₀)
        have hC_pgroup : IsPGroup 5 C := by
          intro y
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
          refine ⟨1, Subtype.ext ?_⟩
          change (y.1 : Q) ^ (5 ^ 1) = 1
          rw [← hk, pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
            zpow_natCast, ← map_pow, hpow1, map_one, _root_.one_zpow]
        obtain ⟨S', hCS'⟩ := hC_pgroup.exists_le_sylow
        rw [Subsingleton.elim S' S₅] at hCS'
        exact hCS' (Subgroup.mem_zpowers (πQ h₀))⟩
    have hemb_inj : Function.Injective emb := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ h
      have hab : a = b := congrArg (fun x : L => x.1) h
      exact Subtype.ext hab
    have hle_L : Nat.card {h : H // orderOf h = 5} ≤ Nat.card L :=
      Nat.card_le_card_of_injective emb hemb_inj
    omega
  · have h13 := card_sylow_mul_pred_le_card_orderOf (H := H) 13 hcard_Q13
    rw [hn13_40] at h13
    let ι : {h : H // orderOf h = 13} ⊕ {h : H // orderOf h = 5} → H :=
      Sum.elim Subtype.val Subtype.val
    have hι_inj : Function.Injective ι := by
      rintro (⟨h₁, ho₁⟩ | ⟨h₁, ho₁⟩) (⟨h₂, ho₂⟩ | ⟨h₂, ho₂⟩) heq
      · exact congrArg Sum.inl (Subtype.ext heq)
      · exfalso
        change h₁ = h₂ at heq
        subst heq
        omega
      · exfalso
        change h₁ = h₂ at heq
        subst heq
        omega
      · exact congrArg Sum.inr (Subtype.ext heq)
    have hsum_le : Nat.card {h : H // orderOf h = 13} + Nat.card {h : H // orderOf h = 5} ≤
        Nat.card H := by
      rw [← Nat.card_sum]
      exact Nat.card_le_card_of_injective ι hι_inj
    rw [hH_card] at hsum_le
    omega

/-- For `q = 9` (`p = 3, f = 2`), either `Nat.card α = 6` or `9 ≤ Nat.card α`. -/
theorem six_or_nine_le_card_of_nine {α : Type*} {K : Type} [Finite α] [Field K] [Finite K]
    {T : Subgroup (Perm α)} [MulAction.IsPretransitive T α]
    (e : T ≃* projectiveSL 2 K) [CharP K 3] (hK : Nat.card K = 9)
    (hS_card : Nat.card (projectiveSL 2 K) = 360) :
    Nat.card α = 6 ∨ 9 ≤ Nat.card α := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h5 : 5 ≤ Nat.card α := by
    have := half_card_add_one_le_card_of_odd e Nat.prime_three le_rfl (by omega)
    omega
  rcases Nat.lt_or_ge (Nat.card α) 9 with hlt9 | hge9
  · left
    obtain ⟨x₀⟩ : Nonempty α := Finite.card_pos_iff.mp (by omega)
    have hdvd_360 : Nat.card α ∣ 360 := hS_card ▸ card_dvd_card_of_pretransitive e x₀
    have hfact : 360 ∣ (Nat.card α).factorial := hS_card ▸ card_dvd_factorial_of_equiv e
    set n := Nat.card α
    have hn_cases : n = 6 ∨ n = 8 := by
      revert hdvd_360 hfact
      interval_cases n <;> decide
    rcases hn_cases with hn6 | hn8
    · exact hn6
    exfalso
    set H := ptStab e x₀
    have hH_card : Nat.card H = 45 := by
      have hmul : Nat.card H * n = Nat.card (projectiveSL 2 K) :=
        card_ptStab_mul_card e x₀
      rw [hn8, hS_card] at hmul
      omega
    obtain ⟨P₃⟩ : Nonempty (Sylow 3 H) := Sylow.nonempty
    obtain ⟨hP₃_card, hP₃_idx⟩ :=
      card_sylow_and_index_eq P₃ (k := 2) (m := 5) (by omega) (by decide)
    have hn3_dvd : Nat.card (Sylow 3 H) ∣ 5 := hP₃_idx ▸ Sylow.card_dvd_index P₃
    have hn3_mod : Nat.card (Sylow 3 H) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 H
    have hn3_1 : Nat.card (Sylow 3 H) = 1 := by
      set m := Nat.card (Sylow 3 H)
      have hm_pos : 0 < m := Nat.card_pos
      have hm_le : m ≤ 5 := Nat.le_of_dvd (by omega) hn3_dvd
      revert hn3_dvd hn3_mod
      interval_cases m <;> decide
    have hP₃_norm : (P₃ : Subgroup H).Normal := normal_of_card_sylow_eq_one hn3_1 P₃
    let P₃_S : Subgroup (projectiveSL 2 K) := (P₃ : Subgroup H).map H.subtype
    have hP₃_S_card : Nat.card P₃_S = 9 := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact hP₃_card
    have hP₃_S_pgroup : IsPGroup 3 P₃_S :=
      IsPGroup.of_card (n := 2) (by rw [hP₃_S_card]; rfl)
    let S₃ : Sylow 3 (projectiveSL 2 K) := hP₃_S_pgroup.toSylow (by
      have h := P₃_S.card_mul_index
      rw [hP₃_S_card, hS_card] at h
      have hidx : P₃_S.index = 40 := by omega
      rw [hidx]
      decide)
    obtain ⟨U₃, hU₃⟩ := exists_sylow_projUnitriangular (K := K) 3 (n := 2) (by omega)
    obtain ⟨s, hs⟩ := MulAction.exists_smul_eq (projectiveSL 2 K) S₃ U₃
    have hconj_P : P₃_S.map (MulAut.conj s : projectiveSL 2 K →* projectiveSL 2 K) =
        projUnitriangular 2 K := by
      rw [← hU₃, ← hs, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    let H' : Subgroup (projectiveSL 2 K) :=
      H.map (MulAut.conj s : projectiveSL 2 K →* projectiveSL 2 K)
    have hH'_card : Nat.card H' = 45 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj s).injective]
      exact hH_card
    have hH'_le_norm : H' ≤ Subgroup.normalizer (projUnitriangular 2 K : Set _) := by
      rintro _ ⟨h, hh, rfl⟩
      rw [← hconj_P, Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        have hp' : (⟨h, hh⟩ : H) * p * (⟨h, hh⟩ : H)⁻¹ ∈ (P₃ : Subgroup H) :=
          hP₃_norm.conj_mem p hp ⟨h, hh⟩
        refine ⟨h * p.1 * h⁻¹, ⟨⟨h, hh⟩ * p * (⟨h, hh⟩ : H)⁻¹, hp', rfl⟩, ?_⟩
        change s * (h * p.1 * h⁻¹) * s⁻¹ = (s * h * s⁻¹) * (s * p.1 * s⁻¹) * (s * h * s⁻¹)⁻¹
        group
      · rintro ⟨_, ⟨p, hp, rfl⟩, hy_eq⟩
        have hp' : (⟨h, hh⟩ : H)⁻¹ * p * (⟨h, hh⟩ : H) ∈ (P₃ : Subgroup H) := by
          simpa using hP₃_norm.conj_mem p hp (⟨h, hh⟩ : H)⁻¹
        refine ⟨h⁻¹ * p.1 * h, ⟨(⟨h, hh⟩ : H)⁻¹ * p * ⟨h, hh⟩, hp', rfl⟩, ?_⟩
        have hy_eq' : s * p.1 * s⁻¹ = (s * h * s⁻¹) * y * (s * h * s⁻¹)⁻¹ := hy_eq
        calc (MulAut.conj s : projectiveSL 2 K →* projectiveSL 2 K) (h⁻¹ * p.1 * h)
          _ = (s * h * s⁻¹)⁻¹ * (s * p.1 * s⁻¹) * (s * h * s⁻¹) := by
              change s * (h⁻¹ * p.1 * h) * s⁻¹ = _
              group
          _ = (s * h * s⁻¹)⁻¹ * ((s * h * s⁻¹) * y * (s * h * s⁻¹)⁻¹) * (s * h * s⁻¹) := by
              rw [hy_eq']
          _ = y := by group
    have hU_ne_bot : projUnitriangular 2 K ≠ ⊥ := by
      intro hbot
      have hcard := card_projUnitriangular (K := K) 2
      rw [hbot, Subgroup.card_bot, hK] at hcard
      omega
    have hH'_le_B : H' ≤ projUpperTriangular 2 K :=
      le_trans hH'_le_norm
        (normalizer_le_projUpperTriangular_of_le_projUnitriangular le_rfl hU_ne_bot)
    have hdvd_B : 45 ∣ Nat.card (projUpperTriangular 2 K) := by
      rw [← hH'_card]
      exact Subgroup.card_dvd_of_le hH'_le_B
    have hdvd_72 : Nat.card (projUpperTriangular 2 K) ∣ 72 := by
      have h := card_projUpperTriangular_two_mul_scalars (K := K)
      rw [hK] at h
      exact ⟨Nat.card (scalars 2 K), h.symm⟩
    have hdvd_45_72 : 45 ∣ 72 := dvd_trans hdvd_B hdvd_72
    revert hdvd_45_72
    decide
  · exact Or.inr hge9

/-- If an element `h ∈ SL(2, K)` commutes with an upper triangular matrix `g ∈ upperTriangular 2 K`
whose diagonal entries are distinct (`g 0 0 ≠ g 1 1`), then `h ∈ upperTriangular 2 K`. -/
theorem mem_upperTriangular_of_comm_of_diag_ne {K : Type*} [Field K]
    {g h : SpecialLinearGroup (Fin 2) K} (hg : g ∈ upperTriangular 2 K)
    (hne : (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ (g : Matrix (Fin 2) (Fin 2) K) 1 1)
    (hcomm : h * g = g * h) :
    h ∈ upperTriangular 2 K := by
  set G : Matrix (Fin 2) (Fin 2) K := (g : Matrix (Fin 2) (Fin 2) K)
  set M : Matrix (Fin 2) (Fin 2) K := (h : Matrix (Fin 2) (Fin 2) K)
  have hg10 : G 1 0 = 0 := hg 1 0 (by decide)
  have hmat : M * G = G * M := congrArg Subtype.val hcomm
  have h10 := congrFun (congrFun hmat 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hg10, mul_zero, zero_mul, add_zero,
    zero_add] at h10
  have hsub : (G 0 0 - G 1 1) * M 1 0 = 0 := by
    linear_combination h10
  have hh10 : M 1 0 = 0 :=
    (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  exact hh10

/-- For `q = 8` (`p = 2, f = 3`), `9 ≤ Nat.card α`. -/
theorem nine_le_card_of_eight {α : Type*} {K : Type} [Finite α] [Field K] [Finite K]
    {T : Subgroup (Perm α)} [MulAction.IsPretransitive T α]
    (e : T ≃* projectiveSL 2 K) [CharP K 2] (hK : Nat.card K = 8)
    (hS_card : Nat.card (projectiveSL 2 K) = 504) :
    9 ≤ Nat.card α := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨x, _, hrel_le, hdvd, hp2, _⟩ := exists_borel_index_two e Nat.prime_two
  set H := ptStab e x
  set idx := H.relIndex (projUpperTriangular 2 K)
  have h8_idx : 8 ≤ idx := by
    rw [← hK]
    exact hp2 rfl
  have h8_n : 8 ≤ Nat.card α := le_trans h8_idx hrel_le
  rcases lt_or_eq_of_le h8_n with h9 | hn8
  · exact h9
  exfalso
  have hsc1 : Nat.card (scalars 2 K) = 1 := by
    have h1 := card_projectiveSL_two_mul_scalars (K := K)
    rw [hS_card, hK] at h1
    have h1' : 504 * Nat.card (scalars 2 K) = 504 := h1
    omega
  have hproj_inj : Function.Injective (proj 2 K) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_proj, ← Subgroup.card_eq_one]
    exact hsc1
  have hH_card : Nat.card H = 63 := by
    have hmul : Nat.card H * Nat.card α = Nat.card (projectiveSL 2 K) :=
      card_ptStab_mul_card e x
    rw [← hn8, hS_card] at hmul
    omega
  have hB_card : Nat.card (projUpperTriangular 2 K) = 56 := by
    have h2 := card_projUpperTriangular_two_mul_scalars (K := K)
    rw [hsc1, hK] at h2
    have h2' : Nat.card (projUpperTriangular 2 K) * 1 = 56 := h2
    omega
  have hidx8 : idx = 8 := le_antisymm (hn8.symm ▸ hrel_le) h8_idx
  obtain ⟨_, _, hHB_mul_raw, _⟩ := relIndex_ptStab_props e (projUpperTriangular 2 K) x
  have hHB_mul : Nat.card ↥(projUpperTriangular 2 K ⊓ H) * idx =
      Nat.card (projUpperTriangular 2 K) := hHB_mul_raw
  rw [hidx8, hB_card] at hHB_mul
  have hHB_card : Nat.card ↥(projUpperTriangular 2 K ⊓ H) = 7 := by omega
  let P₇_sub : Subgroup H := (projUpperTriangular 2 K).subgroupOf H
  have hP₇_card : Nat.card P₇_sub = 7 := by
    rw [card_subgroupOf, hHB_card]
  have hP₇_pgroup : IsPGroup 7 P₇_sub := IsPGroup.of_card (n := 1) (by rw [hP₇_card, pow_one])
  let P₇ : Sylow 7 H := hP₇_pgroup.toSylow (by
    have h := P₇_sub.card_mul_index
    rw [hP₇_card, hH_card] at h
    have hidx : P₇_sub.index = 9 := by omega
    rw [hidx]
    decide)
  have hP₇_idx : P₇_sub.index = 9 := by
    have h := P₇_sub.card_mul_index
    rw [hP₇_card, hH_card] at h
    omega
  have hn7_dvd : Nat.card (Sylow 7 H) ∣ 9 := hP₇_idx ▸ Sylow.card_dvd_index P₇
  have hn7_mod : Nat.card (Sylow 7 H) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 H
  have hn7_1 : Nat.card (Sylow 7 H) = 1 := by
    set m := Nat.card (Sylow 7 H)
    have hm_pos : 0 < m := Nat.card_pos
    have hm_le : m ≤ 9 := Nat.le_of_dvd (by omega) hn7_dvd
    revert hn7_dvd hn7_mod
    interval_cases m <;> decide
  have hP₇_norm : P₇_sub.Normal := normal_of_card_sylow_eq_one hn7_1 P₇
  obtain ⟨P₃⟩ : Nonempty (Sylow 3 H) := Sylow.nonempty
  obtain ⟨hP₃_card_pow, _⟩ :=
    card_sylow_and_index_eq P₃ (k := 2) (m := 7) (by omega) (by decide)
  have hP₃_card : Nat.card P₃ = 9 := hP₃_card_pow
  have hinf_bot : P₇_sub ⊓ (P₃ : Subgroup H) = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have hd1 : Nat.card ↥(P₇_sub ⊓ (P₃ : Subgroup H)) ∣ 7 := by
      rw [← hP₇_card, inf_comm, ← card_subgroupOf (P₃ : Subgroup H) P₇_sub]
      exact Subgroup.card_subgroup_dvd_card _
    have hd2 : Nat.card ↥(P₇_sub ⊓ (P₃ : Subgroup H)) ∣ 9 := by
      rw [← hP₃_card, ← card_subgroupOf P₇_sub (P₃ : Subgroup H)]
      exact Subgroup.card_subgroup_dvd_card _
    exact Nat.dvd_one.mp (Nat.dvd_gcd hd1 hd2)
  have hex_g : ∃ g : P₇_sub, g ≠ 1 := by
    have : Nontrivial P₇_sub := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_ne 1
  obtain ⟨g₀, hg_ne1⟩ := hex_g
  set gH : H := g₀.1
  have hgP₇ : gH ∈ P₇_sub := g₀.2
  obtain ⟨gSL, hgB, hg_eq⟩ := g₀.2
  obtain ⟨⟨w₀, a⟩, hgB_eq⟩ := (upperTriangular2Equiv K).surjective ⟨gSL, hgB⟩
  have hgSL_eq : gSL = uMat2 w₀ * dMat2 a := congrArg Subtype.val hgB_eq.symm
  have h20 : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
  have ha_ne1 : a ≠ 1 := by
    intro ha1
    subst ha1
    have hg_sq1 : gSL * gSL = 1 := by
      rw [hgSL_eq, dMat2_one, mul_one, uMat2_mul, ← two_mul, h20, zero_mul, uMat2_zero]
    have hH_sq1 : g₀ ^ 2 = 1 := by
      rw [sq]
      apply Subtype.ext
      apply Subtype.ext
      have hg_eq' : (g₀.1.1 : projectiveSL 2 K) = proj 2 K gSL := hg_eq.symm
      change (g₀.1.1 : projectiveSL 2 K) * g₀.1.1 = 1
      rw [hg_eq', ← map_mul, hg_sq1, map_one]
    have hdvd2 : orderOf g₀ ∣ 2 := orderOf_dvd_of_pow_eq_one hH_sq1
    have hdvd7 : orderOf g₀ ∣ 7 := by
      rw [← hP₇_card]
      exact orderOf_dvd_natCard g₀
    have hord1 : orderOf g₀ = 1 :=
      Nat.dvd_one.mp (Nat.dvd_gcd hdvd2 hdvd7)
    exact hg_ne1 (orderOf_eq_one_iff.mp hord1)
  have hdiag_ne : (gSL : Matrix (Fin 2) (Fin 2) K) 0 0 ≠
      (gSL : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    have h00 : (gSL : Matrix (Fin 2) (Fin 2) K) 0 0 = (a : K) := by
      rw [hgSL_eq]
      change ((!![1, w₀; 0, 1] : Matrix (Fin 2) (Fin 2) K) *
        !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)]) 0 0 = (a : K)
      simp
    have h11 : (gSL : Matrix (Fin 2) (Fin 2) K) 1 1 = ((a⁻¹ : Kˣ) : K) := by
      rw [hgSL_eq]
      change ((!![1, w₀; 0, 1] : Matrix (Fin 2) (Fin 2) K) *
        !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)]) 1 1 = ((a⁻¹ : Kˣ) : K)
      simp
    rw [h00, h11]
    intro heq
    apply ha_ne1
    apply Units.ext
    have hsq : ((a : K) - 1) ^ 2 = 0 := by
      have ha2 : (a : K) * (a : K) = 1 := by
        calc (a : K) * (a : K) = (a : K) * ((a⁻¹ : Kˣ) : K) := by rw [← heq]
          _ = 1 := Units.mul_inv a
      calc ((a : K) - 1) ^ 2 = (a : K) * (a : K) + 1 - 2 * (a : K) := by ring
        _ = 1 + 1 - 2 * (a : K) := by rw [ha2]
        _ = 0 := by rw [← two_mul, h20]; ring
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  let φ : P₃ → P₇_sub := fun p => ⟨p.1 * gH * p.1⁻¹, hP₇_norm.conj_mem gH hgP₇ p.1⟩
  have hφ_inj : Function.Injective φ := by
    intro p₁ p₂ hp
    have hconj : p₁.1 * gH * p₁.1⁻¹ = p₂.1 * gH * p₂.1⁻¹ := congrArg Subtype.val hp
    set hH : H := p₂.1⁻¹ * p₁.1
    have hhP₃ : hH ∈ (P₃ : Subgroup H) :=
      (P₃ : Subgroup H).mul_mem ((P₃ : Subgroup H).inv_mem p₂.2) p₁.2
    have hcomm_H : hH * gH = gH * hH := by
      calc p₂.1⁻¹ * p₁.1 * gH
        _ = p₂.1⁻¹ * (p₁.1 * gH * p₁.1⁻¹) * p₁.1 := by group
        _ = p₂.1⁻¹ * (p₂.1 * gH * p₂.1⁻¹) * p₁.1 := by rw [hconj]
        _ = gH * (p₂.1⁻¹ * p₁.1) := by group
    obtain ⟨hSL, hh_eq⟩ := proj_surjective 2 K hH.1
    have hcomm_SL : hSL * gSL = gSL * hSL := by
      apply hproj_inj
      rw [map_mul, map_mul, hg_eq, hh_eq]
      exact congrArg Subtype.val hcomm_H
    have hhP₇ : hH ∈ P₇_sub :=
      ⟨hSL, mem_upperTriangular_of_comm_of_diag_ne hgB hdiag_ne hcomm_SL, hh_eq⟩
    have hh_mem_inf : hH ∈ P₇_sub ⊓ (P₃ : Subgroup H) := ⟨hhP₇, hhP₃⟩
    rw [hinf_bot, Subgroup.mem_bot] at hh_mem_inf
    exact Subtype.ext (inv_mul_eq_one.mp hh_mem_inf).symm
  have hle_9_7 : Nat.card P₃ ≤ Nat.card P₇_sub := Nat.card_le_card_of_injective φ hφ_inj
  omega

end Maroti
