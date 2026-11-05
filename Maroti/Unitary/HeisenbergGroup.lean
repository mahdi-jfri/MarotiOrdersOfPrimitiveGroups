module

public import CFSG.ClassicalGroups.Unitary.Simple
public import Maroti.MinDegree.Heisenberg

/-!
# Heisenberg Subgroup of the Special Unitary Group

This file constructs the Heisenberg subgroup `Q₀ = heisSubgroup hσ m` of the special unitary group
`SU σ (m + 2)` (`CFSG/ClassicalGroups/Unitary/Simple.lean`) associated with the hyperbolic pair of
basis vectors `0` and `Fin.rev 0` for the antidiagonal Hermitian form `hermJ` (used in Step 2 of
Maróti, Section 2, page 634). We establish its center `Z₀ = heisCenter hσ m`, commutator and
`p`-th power relations, center index `(heisCenter hσ.invol m).index = (Nat.card K) ^ m`, and
conjugation formulas for diagonal torus elements `diagSU` and middle long-root transvections
`midRoot`.
-/

@[expose] public section

namespace Maroti.Unitary

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open scoped commutatorElement

variable {K : Type*} [Field K]

section FormJ

variable (σ : K ≃+* K) {n : ℕ}

/-- Antidiagonal Hermitian form `∑ i, σ (x i) * y (Fin.rev i)` for `SU σ n`. -/
def hermJ (x y : Fin n → K) : K := ∑ i, σ (x i) * y (Fin.rev i)

theorem antidiag_mulVec (y : Fin n → K) :
    (antidiag n : Matrix (Fin n) (Fin n) K) *ᵥ y = fun i => y (Fin.rev i) := by
  funext i
  simp only [mulVec, dotProduct, antidiag, of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (Fin.rev i) (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem hermJ_eq_herm_antidiag (x y : Fin n → K) :
    hermJ σ x y = herm σ x ((antidiag n : Matrix (Fin n) (Fin n) K) *ᵥ y) := by
  rw [hermJ, herm, antidiag_mulVec]

@[simp] theorem hermJ_add_left (x x' y : Fin n → K) :
    hermJ σ (x + x') y = hermJ σ x y + hermJ σ x' y := by
  simp only [hermJ_eq_herm_antidiag, herm_add_left]

@[simp] theorem hermJ_add_right (x y y' : Fin n → K) :
    hermJ σ x (y + y') = hermJ σ x y + hermJ σ x y' := by
  simp only [hermJ_eq_herm_antidiag, mulVec_add, herm_add_right]

@[simp] theorem hermJ_smul_left (c : K) (x y : Fin n → K) :
    hermJ σ (c • x) y = σ c * hermJ σ x y := by
  simp only [hermJ_eq_herm_antidiag, herm_smul_left]

@[simp] theorem hermJ_smul_right (c : K) (x y : Fin n → K) :
    hermJ σ x (c • y) = c * hermJ σ x y := by
  simp only [hermJ_eq_herm_antidiag, mulVec_smul, herm_smul_right]

@[simp] theorem hermJ_neg_left (x y : Fin n → K) : hermJ σ (-x) y = -hermJ σ x y := by
  simp only [hermJ_eq_herm_antidiag, herm_neg_left]

@[simp] theorem hermJ_neg_right (x y : Fin n → K) : hermJ σ x (-y) = -hermJ σ x y := by
  simp only [hermJ_eq_herm_antidiag, mulVec_neg, herm_neg_right]

@[simp] theorem hermJ_sub_left (x x' y : Fin n → K) :
    hermJ σ (x - x') y = hermJ σ x y - hermJ σ x' y := by
  simp only [hermJ_eq_herm_antidiag, herm_sub_left]

@[simp] theorem hermJ_sub_right (x y y' : Fin n → K) :
    hermJ σ x (y - y') = hermJ σ x y - hermJ σ x y' := by
  simp only [hermJ_eq_herm_antidiag, mulVec_sub, herm_sub_right]

@[simp] theorem hermJ_zero_left (y : Fin n → K) : hermJ σ 0 y = 0 := by
  simp only [hermJ_eq_herm_antidiag, herm_zero_left]

@[simp] theorem hermJ_zero_right (x : Fin n → K) : hermJ σ x 0 = 0 := by
  simp only [hermJ_eq_herm_antidiag, mulVec_zero, herm_zero_right]

theorem hermJ_single_left (i : Fin n) (c : K) (y : Fin n → K) :
    hermJ σ (Pi.single i c) y = σ c * y (Fin.rev i) := by
  rw [hermJ_eq_herm_antidiag, herm_single_left, antidiag_mulVec]

theorem hermJ_single_right (x : Fin n → K) (i : Fin n) (c : K) :
    hermJ σ x (Pi.single i c) = σ (x (Fin.rev i)) * c := by
  rw [hermJ, Finset.sum_eq_single (Fin.rev i)]
  · simp [Fin.rev_rev]
  · intro j _ hj
    have hj' : Fin.rev j ≠ i := fun h => hj (by rw [← h, Fin.rev_rev])
    simp [Pi.single_eq_of_ne hj']
  · simp

theorem hermJ_conj' (hσ : ∀ c, σ (σ c) = c) (x y : Fin n → K) :
    σ (hermJ σ x y) = hermJ σ y x := by
  rw [hermJ, hermJ, map_sum, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [map_mul, hσ, mul_comm]

theorem hermJ_conj (hσ : ∀ c, σ (σ c) = c) (x y : Fin n → K) :
    hermJ σ y x = σ (hermJ σ x y) :=
  (hermJ_conj' σ hσ x y).symm

theorem hermJ_self_fixed (hσ : ∀ c, σ (σ c) = c) (x : Fin n → K) :
    σ (hermJ σ x x) = hermJ σ x x :=
  hermJ_conj' σ hσ x x

theorem hermJ_eq_zero_comm (hσ : ∀ c, σ (σ c) = c) {x y : Fin n → K} (h : hermJ σ x y = 0) :
    hermJ σ y x = 0 := by
  rw [← hermJ_conj' σ hσ, h, map_zero]

theorem hermJ_mulVec (A : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    hermJ σ (A *ᵥ x) (A *ᵥ y) =
      herm σ x ((conjTr σ A * antidiag n * A) *ᵥ y) := by
  have h1 : (fun i => σ ((A *ᵥ x) i)) = A.map σ *ᵥ fun i => σ (x i) := by
    funext i
    simp [mulVec, dotProduct, map_sum]
  have e1 : hermJ σ (A *ᵥ x) (A *ᵥ y) =
      (fun i => σ ((A *ᵥ x) i)) ⬝ᵥ ((antidiag n * A) *ᵥ y) := by
    rw [hermJ_eq_herm_antidiag, mulVec_mulVec]; rfl
  have e2 : herm σ x ((conjTr σ A * antidiag n * A) *ᵥ y) =
      (fun i => σ (x i)) ⬝ᵥ (conjTr σ A *ᵥ ((antidiag n * A) *ᵥ y)) := by
    rw [Matrix.mul_assoc, ← mulVec_mulVec]; rfl
  rw [e1, e2, h1, conjTr, dotProduct_mulVec (fun i => σ (x i)), vecMul_transpose]

theorem conjTr_mul_antidiag_mul_self_of_isometry {A : Matrix (Fin n) (Fin n) K}
    (h : ∀ x y, hermJ σ (A *ᵥ x) (A *ᵥ y) = hermJ σ x y) :
    conjTr σ A * antidiag n * A = antidiag n := by
  ext j k
  have hjk := h (Pi.single j 1) (Pi.single k 1)
  rw [hermJ_mulVec, herm_single_left, map_one, one_mul, mulVec_single_one,
    hermJ_eq_herm_antidiag, herm_single_left, map_one, one_mul, mulVec_single_one] at hjk
  exact hjk

theorem mem_SU_iff {B : GL (Fin n) K} :
    B ∈ SU σ n ↔ (B : Matrix (Fin n) (Fin n) K).det = 1 ∧
      ∀ x y, hermJ σ ((B : Matrix (Fin n) (Fin n) K) *ᵥ x)
        ((B : Matrix (Fin n) (Fin n) K) *ᵥ y) = hermJ σ x y := by
  rw [mem_SU]
  refine and_congr_right fun _ => ⟨fun h x y => ?_, conjTr_mul_antidiag_mul_self_of_isometry σ⟩
  rw [hermJ_mulVec, h, ← hermJ_eq_herm_antidiag]

instance instSMulSU : SMul (SU σ n) (Fin n → K) := inferInstance
instance instMulActionSU : MulAction (SU σ n) (Fin n → K) := inferInstance
instance instDistribMulActionSU : DistribMulAction (SU σ n) (Fin n → K) := inferInstance
instance instSMulCommClassSU : SMulCommClass (SU σ n) K (Fin n → K) := inferInstance

/-- Construct an element of `SU σ n` from its matrix, determinant, and `hermJ`-isometry. -/
noncomputable def mkSUJ (M : Matrix (Fin n) (Fin n) K) (hdet : M.det = 1)
    (hiso : ∀ x y, hermJ σ (M *ᵥ x) (M *ᵥ y) = hermJ σ x y) : SU σ n :=
  ⟨GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero),
    (mem_SU_iff σ).mpr ⟨hdet, hiso⟩⟩

theorem smul_SU_def (g : SU σ n) (v : Fin n → K) :
    g • v = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v := rfl

@[simp] theorem mkSUJ_smul (M : Matrix (Fin n) (Fin n) K) (hdet : M.det = 1)
    (hiso : ∀ x y, hermJ σ (M *ᵥ x) (M *ᵥ y) = hermJ σ x y) (v : Fin n → K) :
    mkSUJ σ M hdet hiso • v = M *ᵥ v := rfl

theorem hermJ_smul_smul (g : SU σ n) (x y : Fin n → K) :
    hermJ σ (g • x) (g • y) = hermJ σ x y :=
  ((mem_SU_iff σ).mp g.2).2 x y

theorem ext_smul_SU {g g' : SU σ n} (H : ∀ v : Fin n → K, g • v = g' • v) : g = g' :=
  Subtype.ext (Units.ext (Matrix.ext_of_mulVec_single fun _ => H _))

variable {σ}

/-- Adjoint vector `i ↦ σ (w (Fin.rev i))` for rank-one operators with respect to `hermJ`. -/
def vecJ (σ : K ≃+* K) (w : Fin n → K) : Fin n → K := fun i => σ (w (Fin.rev i))

theorem dotProduct_vecJ (w z : Fin n → K) : vecJ σ w ⬝ᵥ z = hermJ σ w z := by
  rw [dotProduct, hermJ, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [vecJ]

theorem one_add_vecMulVec_vecJ_mulVec (u w z : Fin n → K) :
    (1 + vecMulVec u (vecJ σ w)) *ᵥ z = z + hermJ σ w z • u := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, dotProduct_vecJ,
    op_smul_eq_smul]

/-- Transvection matrix in `SU σ n` along an isotropic vector `a`. -/
noncomputable def tvMatJ (σ : K ≃+* K) (a : Fin n → K) (c : K) : Matrix (Fin n) (Fin n) K :=
  1 + c • vecMulVec a (vecJ σ a)

theorem tvMatJ_mulVec (a : Fin n → K) (c : K) (v : Fin n → K) :
    tvMatJ σ a c *ᵥ v = v + (c * hermJ σ a v) • a := by
  rw [tvMatJ, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, dotProduct_vecJ, op_smul_eq_smul, smul_smul]

theorem tvMatJ_det {a : Fin n → K} (ha : hermJ σ a a = 0) (c : K) :
    (tvMatJ σ a c).det = 1 := by
  rw [tvMatJ, ← Matrix.vecMulVec_smul, Matrix.vecMulVec_eq (Fin 1),
    Matrix.det_one_add_replicateCol_mul_replicateRow, smul_dotProduct, dotProduct_vecJ,
    smul_eq_mul, ha, mul_zero, add_zero]

theorem tvMatJ_isometry (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : hermJ σ a a = 0) (c : K)
    (hc : c + σ c = 0) (x y : Fin n → K) :
    hermJ σ (tvMatJ σ a c *ᵥ x) (tvMatJ σ a c *ᵥ y) = hermJ σ x y := by
  rw [tvMatJ_mulVec, tvMatJ_mulVec]
  simp only [hermJ_add_left, hermJ_add_right, hermJ_smul_left, hermJ_smul_right, ha, map_mul,
    mul_zero, add_zero, ← hermJ_conj' σ hσ a x]
  linear_combination σ (hermJ σ a x) * hermJ σ a y * hc

/-- Unitary transvection `v ↦ v + (c * hermJ σ a v) • a` in `SU σ n`. -/
noncomputable def tvJ (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : hermJ σ a a = 0)
    (c : K) (hc : c + σ c = 0) : SU σ n :=
  mkSUJ σ (tvMatJ σ a c) (tvMatJ_det ha c) (tvMatJ_isometry hσ ha c hc)

theorem tvJ_smul (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : hermJ σ a a = 0) (c : K)
    (hc : c + σ c = 0) (v : Fin n → K) :
    tvJ hσ ha c hc • v = v + (c * hermJ σ a v) • a :=
  tvMatJ_mulVec a c v

/-- Eichler matrix in `SU σ n` for an isotropic vector `e` and orthogonal vector `y`. -/
noncomputable def eichlerMatJ (σ : K ≃+* K) (e y : Fin n → K) (c : K) :
    Matrix (Fin n) (Fin n) K :=
  (1 + vecMulVec (y + c • e) (vecJ σ e)) * (1 + vecMulVec (-e) (vecJ σ y))

theorem eichlerMatJ_mulVec {e y : Fin n → K} (he : hermJ σ e e = 0) (c : K) (x : Fin n → K) :
    eichlerMatJ σ e y c *ᵥ x = x + hermJ σ e x • (y + c • e) - hermJ σ y x • e := by
  rw [eichlerMatJ, ← Matrix.mulVec_mulVec, one_add_vecMulVec_vecJ_mulVec,
    one_add_vecMulVec_vecJ_mulVec]
  simp only [hermJ_add_right, hermJ_smul_right, hermJ_neg_right, he, mul_zero, neg_zero, add_zero]
  module

theorem eichlerMatJ_det (hσ : ∀ c, σ (σ c) = c) {e y : Fin n → K} (he : hermJ σ e e = 0)
    (hey : hermJ σ e y = 0) (c : K) : (eichlerMatJ σ e y c).det = 1 := by
  have h1 : vecJ σ e ⬝ᵥ (y + c • e) = hermJ σ e (y + c • e) := dotProduct_vecJ e (y + c • e)
  have h2 : vecJ σ y ⬝ᵥ (-e) = hermJ σ y (-e) := dotProduct_vecJ y (-e)
  rw [eichlerMatJ, Matrix.det_mul, Matrix.vecMulVec_eq (Fin 1), Matrix.vecMulVec_eq (Fin 1),
    Matrix.det_one_add_replicateCol_mul_replicateRow,
    Matrix.det_one_add_replicateCol_mul_replicateRow,
    h1, h2, hermJ_add_right, hermJ_smul_right, he, hey,
    hermJ_neg_right, hermJ_eq_zero_comm σ hσ hey]
  ring

theorem eichlerJ_isometry (hσ : ∀ c, σ (σ c) = c) {e y : Fin n → K} (he : hermJ σ e e = 0)
    (hey : hermJ σ e y = 0) (c : K) (hc : c + σ c = -hermJ σ y y) (x x' : Fin n → K) :
    hermJ σ (x + hermJ σ e x • (y + c • e) - hermJ σ y x • e)
      (x' + hermJ σ e x' • (y + c • e) - hermJ σ y x' • e) = hermJ σ x x' := by
  have hye : hermJ σ y e = 0 := hermJ_eq_zero_comm σ hσ hey
  simp only [hermJ_add_left, hermJ_add_right, hermJ_sub_left, hermJ_sub_right, hermJ_smul_left,
    hermJ_smul_right, he, hey, hye, mul_zero, add_zero, sub_zero]
  simp only [← hermJ_conj' σ hσ e x, ← hermJ_conj' σ hσ x y, hσ]
  linear_combination σ (hermJ σ e x) * hermJ σ e x' * hc

/-- Eichler transformation in `SU σ n`. -/
noncomputable def eichlerJ (hσ : ∀ c, σ (σ c) = c) {e y : Fin n → K}
    (he : hermJ σ e e = 0) (hey : hermJ σ e y = 0) (c : K) (hc : c + σ c = -hermJ σ y y) :
    SU σ n :=
  mkSUJ σ (eichlerMatJ σ e y c) (eichlerMatJ_det hσ he hey c) fun x x' => by
    rw [eichlerMatJ_mulVec he, eichlerMatJ_mulVec he]
    exact eichlerJ_isometry hσ he hey c hc x x'

theorem eichlerJ_smul (hσ : ∀ c, σ (σ c) = c) {e y : Fin n → K} (he : hermJ σ e e = 0)
    (hey : hermJ σ e y = 0) (c : K) (hc : c + σ c = -hermJ σ y y) (x : Fin n → K) :
    eichlerJ hσ he hey c hc • x = x + hermJ σ e x • (y + c • e) - hermJ σ y x • e :=
  eichlerMatJ_mulVec he c x

theorem eichlerJ_zero (hσ : ∀ c, σ (σ c) = c) {e : Fin n → K} (he : hermJ σ e e = 0)
    (c : K) (hc : c + σ c = 0) :
    eichlerJ hσ he (hermJ_zero_right σ e) c (by rw [hermJ_zero_left, neg_zero]; exact hc) =
      tvJ hσ he c hc := by
  apply ext_smul_SU
  intro x
  rw [eichlerJ_smul, tvJ_smul, hermJ_zero_left, zero_add, zero_smul, sub_zero, smul_smul,
    mul_comm]

theorem eichlerJ_mul (hσ : ∀ c, σ (σ c) = c) {e y₁ y₂ : Fin n → K} (he : hermJ σ e e = 0)
    (hey₁ : hermJ σ e y₁ = 0) (hey₂ : hermJ σ e y₂ = 0) (c₁ c₂ : K)
    (hc₁ : c₁ + σ c₁ = -hermJ σ y₁ y₁) (hc₂ : c₂ + σ c₂ = -hermJ σ y₂ y₂) :
    eichlerJ hσ he hey₁ c₁ hc₁ * eichlerJ hσ he hey₂ c₂ hc₂ =
      eichlerJ hσ he (y := y₁ + y₂) (by rw [hermJ_add_right, hey₁, hey₂, add_zero])
        (c₁ + c₂ - hermJ σ y₁ y₂) (by
          rw [map_sub, map_add, hermJ_conj' σ hσ y₁ y₂, hermJ_add_left,
            hermJ_add_right, hermJ_add_right]
          linear_combination hc₁ + hc₂) := by
  have hy₁e : hermJ σ y₁ e = 0 := hermJ_eq_zero_comm σ hσ hey₁
  apply ext_smul_SU
  intro x
  rw [mul_smul, eichlerJ_smul, eichlerJ_smul, eichlerJ_smul]
  simp only [hermJ_add_left, hermJ_add_right, hermJ_sub_right, hermJ_smul_right,
    he, hey₂, hy₁e, mul_zero, add_zero, sub_zero]
  module

/-- Diagonal matrix in `SU σ n`. -/
noncomputable def diagSU (t : Fin n → K) (hdet : ∏ i, t i = 1)
    (hiso : ∀ i, σ (t i) * t (Fin.rev i) = 1) : SU σ n :=
  mkSUJ σ (diagonal t) (by rw [det_diagonal, hdet]) fun x y => by
    simp only [hermJ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mulVec_diagonal, mulVec_diagonal, map_mul]
    calc σ (t i) * σ (x i) * (t (Fin.rev i) * y (Fin.rev i))
        = (σ (t i) * t (Fin.rev i)) * (σ (x i) * y (Fin.rev i)) := by ring
      _ = σ (x i) * y (Fin.rev i) := by rw [hiso i, one_mul]

@[simp] theorem diagSU_smul_apply (t : Fin n → K) (hdet : ∏ i, t i = 1)
    (hiso : ∀ i, σ (t i) * t (Fin.rev i) = 1) (v : Fin n → K) (i : Fin n) :
    (diagSU t hdet hiso • v) i = t i * v i :=
  mulVec_diagonal t v i

end FormJ

section HeisenbergSubgroup

variable {σ : K ≃+* K} {m : ℕ}

variable (K) in
/-- First hyperbolic basis vector `e_0` in `Fin (m + 2) → K`. -/
def hypE (m : ℕ) : Fin (m + 2) → K := Pi.single 0 1

variable (K) in
/-- Last hyperbolic basis vector `e_{Fin.rev 0}` in `Fin (m + 2) → K`. -/
def hypF (m : ℕ) : Fin (m + 2) → K := Pi.single (Fin.rev 0) 1

/-- Middle index embedding `Fin m → Fin (m + 2)` avoiding `0` and `Fin.rev 0`. -/
def mid (j : Fin m) : Fin (m + 2) := j.castSucc.succ

theorem zero_ne_rev_zero : (0 : Fin (m + 2)) ≠ Fin.rev 0 := by
  intro h
  have := congrArg Fin.val h
  simp at this

theorem mid_ne_zero (j : Fin m) : mid j ≠ 0 := Fin.succ_ne_zero _

theorem mid_ne_rev_zero (j : Fin m) : mid j ≠ Fin.rev 0 := by
  intro h
  have := congrArg Fin.val h
  have hj := j.isLt
  simp [mid] at this
  omega

theorem rev_mid (j : Fin m) : Fin.rev (mid j) = mid (Fin.rev j) := by
  ext
  have hj := j.isLt
  simp [mid, Fin.val_rev]
  omega

theorem mid_injective : Function.Injective (mid (m := m)) :=
  (Fin.succ_injective _).comp (Fin.castSucc_injective _)

theorem hermJ_hypE_left (y : Fin (m + 2) → K) :
    hermJ σ (hypE K m) y = y (Fin.rev 0) := by
  rw [hypE, hermJ_single_left, map_one, one_mul]

theorem hermJ_hypF_left (y : Fin (m + 2) → K) :
    hermJ σ (hypF K m) y = y 0 := by
  rw [hypF, hermJ_single_left, Fin.rev_rev, map_one, one_mul]

theorem hermJ_hypE_self : hermJ σ (hypE K m) (hypE K m) = 0 := by
  rw [hermJ_hypE_left, hypE, Pi.single_eq_of_ne (Ne.symm zero_ne_rev_zero)]

theorem hermJ_hypF_self : hermJ σ (hypF K m) (hypF K m) = 0 := by
  rw [hermJ_hypF_left, hypF, Pi.single_eq_of_ne zero_ne_rev_zero]

theorem hermJ_hypE_hypF : hermJ σ (hypE K m) (hypF K m) = 1 := by
  rw [hermJ_hypE_left, hypF, Pi.single_eq_same]

theorem hermJ_hypF_hypE : hermJ σ (hypF K m) (hypE K m) = 1 := by
  rw [hermJ_hypF_left, hypE, Pi.single_eq_same]

/-- Embedding of `v : Fin m → K` into the middle coordinates of `Fin (m + 2) → K`. -/
def embMid (v : Fin m → K) : Fin (m + 2) → K :=
  fun i => if h0 : i = 0 then 0 else if h1 : i = Fin.rev 0 then 0 else
    v ⟨i.val - 1, by
      have hi := i.isLt
      have h0' : i.val ≠ 0 := fun h => h0 (Fin.ext h)
      have h1' : i.val ≠ m + 1 := fun h => h1 (Fin.ext (by simp [h]))
      omega⟩

@[simp] theorem embMid_zero (v : Fin m → K) : embMid v 0 = 0 := by simp [embMid]

@[simp] theorem embMid_rev_zero (v : Fin m → K) : embMid v (Fin.rev 0) = 0 := by
  simp [embMid]

@[simp] theorem embMid_mid (v : Fin m → K) (j : Fin m) : embMid v (mid j) = v j := by
  simp [embMid, mid]

theorem embMid_eq_of_zero {y : Fin (m + 2) → K} (h0 : y 0 = 0) (h1 : y (Fin.rev 0) = 0) :
    embMid (fun j => y (mid j)) = y := by
  funext i
  by_cases hi0 : i = 0
  · subst hi0; rw [embMid_zero, h0]
  · by_cases hi1 : i = Fin.rev 0
    · subst hi1; rw [embMid_rev_zero, h1]
    · simp only [embMid, hi0, hi1, ↓reduceDIte]
      congr 1
      ext
      have : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      simp [mid]
      omega

@[simp] theorem embMid_zero_vec : embMid (0 : Fin m → K) = 0 := by
  funext i; simp [embMid]

@[simp] theorem embMid_add (v w : Fin m → K) : embMid (v + w) = embMid v + embMid w := by
  funext i; simp [embMid]; split_ifs <;> simp

@[simp] theorem embMid_neg (v : Fin m → K) : embMid (-v) = -embMid v := by
  funext i; simp [embMid]; split_ifs <;> simp

@[simp] theorem embMid_sub (v w : Fin m → K) : embMid (v - w) = embMid v - embMid w := by
  funext i; simp [embMid]; split_ifs <;> simp

@[simp] theorem embMid_smul (c : K) (v : Fin m → K) : embMid (c • v) = c • embMid v := by
  funext i
  simp only [embMid, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem embMid_single (j : Fin m) (c : K) :
    embMid (Pi.single j c) = Pi.single (mid j) c := by
  have h0 : (Pi.single (mid j) c : Fin (m + 2) → K) 0 = 0 := by
    rw [Pi.single_eq_of_ne (Ne.symm (mid_ne_zero j))]
  have h1 : (Pi.single (mid j) c : Fin (m + 2) → K) (Fin.rev 0) = 0 := by
    rw [Pi.single_eq_of_ne (Ne.symm (mid_ne_rev_zero j))]
  rw [← embMid_eq_of_zero h0 h1]
  congr 1
  funext k
  by_cases hkj : k = j
  · subst hkj; simp
  · rw [Pi.single_eq_of_ne hkj, Pi.single_eq_of_ne (fun h => hkj (mid_injective h))]

theorem hermJ_hypE_embMid (v : Fin m → K) : hermJ σ (hypE K m) (embMid v) = 0 := by
  rw [hermJ_hypE_left, embMid_rev_zero]

theorem hermJ_hypF_embMid (v : Fin m → K) : hermJ σ (hypF K m) (embMid v) = 0 := by
  rw [hermJ_hypF_left, embMid_zero]

theorem hermJ_embMid_hypE (v : Fin m → K) : hermJ σ (embMid v) (hypE K m) = 0 := by
  rw [hypE, hermJ_single_right, embMid_rev_zero, map_zero, zero_mul]

theorem hermJ_embMid_hypF (v : Fin m → K) : hermJ σ (embMid v) (hypF K m) = 0 := by
  rw [hypF, hermJ_single_right, Fin.rev_rev, embMid_zero, map_zero, zero_mul]

theorem hermJ_embMid_embMid (v w : Fin m → K) :
    hermJ σ (embMid v) (embMid w) = hermJ σ v w := by
  rw [hermJ, Fin.sum_univ_succ, embMid_zero, map_zero, zero_mul, zero_add]
  rw [Fin.sum_univ_castSucc]
  have hlast : (Fin.last m).succ = Fin.rev (0 : Fin (m + 2)) := by
    ext; simp
  rw [hlast, embMid_rev_zero, map_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  change σ (embMid v (mid j)) * embMid w (Fin.rev (mid j)) = σ (v j) * w (Fin.rev j)
  rw [rev_mid, embMid_mid, embMid_mid]

/-- Heisenberg element `heis (v, c)` in `SU σ (m + 2)` parameterized by `v : Fin m → K` and
`c : K` with `c + σ c = -hermJ σ v v`. -/
noncomputable def heis (hσ : ∀ c, σ (σ c) = c) (v : Fin m → K) (c : K)
    (hc : c + σ c = -hermJ σ v v) : SU σ (m + 2) :=
  eichlerJ hσ hermJ_hypE_self (hermJ_hypE_embMid v) c
    (by rw [hermJ_embMid_embMid]; exact hc)

theorem heis_smul (hσ : ∀ c, σ (σ c) = c) (v : Fin m → K) (c : K)
    (hc : c + σ c = -hermJ σ v v) (x : Fin (m + 2) → K) :
    heis hσ v c hc • x =
      x + hermJ σ (hypE K m) x • (embMid v + c • hypE K m) -
        hermJ σ (embMid v) x • hypE K m :=
  eichlerJ_smul hσ hermJ_hypE_self (hermJ_hypE_embMid v) c _ x

theorem heis_smul_hypF (hσ : ∀ c, σ (σ c) = c) (v : Fin m → K) (c : K)
    (hc : c + σ c = -hermJ σ v v) :
    heis hσ v c hc • hypF K m = hypF K m + embMid v + c • hypE K m := by
  rw [heis_smul, hermJ_hypE_hypF, hermJ_embMid_hypF, one_smul, zero_smul, sub_zero, add_assoc]

theorem heis_smul_hypF_mid (hσ : ∀ c, σ (σ c) = c) (v : Fin m → K) (c : K)
    (hc : c + σ c = -hermJ σ v v) (j : Fin m) :
    (heis hσ v c hc • hypF K m) (mid j) = v j := by
  rw [heis_smul_hypF, Pi.add_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    hypF, Pi.single_eq_of_ne (mid_ne_rev_zero j),
    hypE, Pi.single_eq_of_ne (mid_ne_zero j), embMid_mid]
  ring

theorem hermJ_hypF_heis_smul_hypF (hσ : ∀ c, σ (σ c) = c) (v : Fin m → K) (c : K)
    (hc : c + σ c = -hermJ σ v v) :
    hermJ σ (hypF K m) (heis hσ v c hc • hypF K m) = c := by
  rw [heis_smul_hypF, hermJ_add_right, hermJ_add_right, hermJ_hypF_self, hermJ_hypF_embMid,
    hermJ_smul_right, hermJ_hypF_hypE]
  ring

theorem heis_ext_iff (hσ : ∀ c, σ (σ c) = c) {v₁ v₂ : Fin m → K} {c₁ c₂ : K}
    (hc₁ : c₁ + σ c₁ = -hermJ σ v₁ v₁) (hc₂ : c₂ + σ c₂ = -hermJ σ v₂ v₂) :
    heis hσ v₁ c₁ hc₁ = heis hσ v₂ c₂ hc₂ ↔ v₁ = v₂ ∧ c₁ = c₂ := by
  constructor
  · intro h
    refine ⟨funext fun j => ?_, ?_⟩
    · rw [← heis_smul_hypF_mid hσ v₁ c₁ hc₁ j, ← heis_smul_hypF_mid hσ v₂ c₂ hc₂ j, h]
    · rw [← hermJ_hypF_heis_smul_hypF hσ v₁ c₁ hc₁, ← hermJ_hypF_heis_smul_hypF hσ v₂ c₂ hc₂, h]
  · rintro ⟨rfl, rfl⟩
    rfl

theorem heis_zero_zero (hσ : ∀ c, σ (σ c) = c) :
    heis (m := m) hσ 0 0 (by simp) = 1 := by
  apply ext_smul_SU
  intro x
  rw [heis_smul]
  simp

theorem heis_mul (hσ : ∀ c, σ (σ c) = c) (v₁ v₂ : Fin m → K) (c₁ c₂ : K)
    (hc₁ : c₁ + σ c₁ = -hermJ σ v₁ v₁) (hc₂ : c₂ + σ c₂ = -hermJ σ v₂ v₂) :
    heis hσ v₁ c₁ hc₁ * heis hσ v₂ c₂ hc₂ =
      heis hσ (v₁ + v₂) (c₁ + c₂ - hermJ σ v₁ v₂) (by
        rw [map_sub, map_add, hermJ_conj' σ hσ v₁ v₂, hermJ_add_left,
          hermJ_add_right, hermJ_add_right]
        linear_combination hc₁ + hc₂) := by
  apply ext_smul_SU
  intro x
  rw [mul_smul, heis_smul, heis_smul, heis_smul, embMid_add]
  simp only [hermJ_add_left, hermJ_add_right, hermJ_sub_right, hermJ_smul_right,
    hermJ_hypE_self, hermJ_hypE_embMid, hermJ_embMid_hypE, hermJ_embMid_embMid,
    mul_zero, add_zero, sub_zero]
  module

theorem heis_inv (hσ : ∀ c, σ (σ c) = c) (v : Fin m → K) (c : K)
    (hc : c + σ c = -hermJ σ v v) :
    (heis hσ v c hc)⁻¹ =
      heis hσ (-v) (-c - hermJ σ v v) (by
        rw [map_sub, map_neg, hermJ_self_fixed σ hσ v, hermJ_neg_left, hermJ_neg_right, neg_neg]
        linear_combination -hc) := by
  apply mul_left_cancel (a := heis hσ v c hc)
  rw [mul_inv_cancel, heis_mul]
  have h1 : v + -v = 0 := add_neg_cancel v
  have h2 : c + (-c - hermJ σ v v) - hermJ σ v (-v) = 0 := by
    rw [hermJ_neg_right]; ring
  rw [(heis_ext_iff hσ _ (by simp)).mpr ⟨h1, h2⟩, heis_zero_zero]

/-- The Heisenberg subgroup `Q₀ ≤ SU σ (m + 2)`. -/
noncomputable def heisSubgroup (hσ : ∀ c, σ (σ c) = c) (m : ℕ) : Subgroup (SU σ (m + 2)) where
  carrier := {g | ∃ (v : Fin m → K) (c : K) (hc : c + σ c = -hermJ σ v v), g = heis hσ v c hc}
  mul_mem' := by
    rintro _ _ ⟨v₁, c₁, hc₁, rfl⟩ ⟨v₂, c₂, hc₂, rfl⟩
    exact ⟨v₁ + v₂, c₁ + c₂ - hermJ σ v₁ v₂, _, heis_mul hσ v₁ v₂ c₁ c₂ hc₁ hc₂⟩
  one_mem' := ⟨0, 0, by simp, (heis_zero_zero hσ).symm⟩
  inv_mem' := by
    rintro _ ⟨v, c, hc, rfl⟩
    exact ⟨-v, -c - hermJ σ v v, _, heis_inv hσ v c hc⟩

/-- Construct an element of `heisSubgroup` from `(v, c)`. -/
noncomputable def mkHeis (hσ : ∀ c, σ (σ c) = c) (v : Fin m → K) (c : K)
    (hc : c + σ c = -hermJ σ v v) : heisSubgroup hσ m :=
  ⟨heis hσ v c hc, v, c, hc, rfl⟩

@[simp] theorem coe_mkHeis (hσ : ∀ c, σ (σ c) = c) (v : Fin m → K) (c : K)
    (hc : c + σ c = -hermJ σ v v) :
    (mkHeis hσ v c hc : SU σ (m + 2)) = heis hσ v c hc := rfl

theorem mkHeis_ext_iff (hσ : ∀ c, σ (σ c) = c) {v₁ v₂ : Fin m → K} {c₁ c₂ : K}
    (hc₁ : c₁ + σ c₁ = -hermJ σ v₁ v₁) (hc₂ : c₂ + σ c₂ = -hermJ σ v₂ v₂) :
    mkHeis hσ v₁ c₁ hc₁ = mkHeis hσ v₂ c₂ hc₂ ↔ v₁ = v₂ ∧ c₁ = c₂ :=
  Subtype.ext_iff.trans (heis_ext_iff hσ hc₁ hc₂)

theorem mkHeis_mul (hσ : ∀ c, σ (σ c) = c) (v₁ v₂ : Fin m → K) (c₁ c₂ : K)
    (hc₁ : c₁ + σ c₁ = -hermJ σ v₁ v₁) (hc₂ : c₂ + σ c₂ = -hermJ σ v₂ v₂) :
    mkHeis hσ v₁ c₁ hc₁ * mkHeis hσ v₂ c₂ hc₂ =
      mkHeis hσ (v₁ + v₂) (c₁ + c₂ - hermJ σ v₁ v₂) (by
        rw [map_sub, map_add, hermJ_conj' σ hσ v₁ v₂, hermJ_add_left,
          hermJ_add_right, hermJ_add_right]
        linear_combination hc₁ + hc₂) :=
  Subtype.ext (heis_mul hσ v₁ v₂ c₁ c₂ hc₁ hc₂)

theorem mkHeis_inv (hσ : ∀ c, σ (σ c) = c) (v : Fin m → K) (c : K)
    (hc : c + σ c = -hermJ σ v v) :
    (mkHeis hσ v c hc)⁻¹ =
      mkHeis hσ (-v) (-c - hermJ σ v v) (by
        rw [map_sub, map_neg, hermJ_self_fixed σ hσ v, hermJ_neg_left, hermJ_neg_right, neg_neg]
        linear_combination -hc) :=
  Subtype.ext (heis_inv hσ v c hc)

/-- Projection `heisSubgroup hσ m →* Multiplicative (Fin m → K)` sending `mkHeis v c` to `v`. -/
noncomputable def heisProj (hσ : ∀ c, σ (σ c) = c) (m : ℕ) :
    heisSubgroup hσ m →* Multiplicative (Fin m → K) where
  toFun q := Multiplicative.ofAdd (fun j => ((q : SU σ (m + 2)) • hypF K m) (mid j))
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext j
    change ((1 : SU σ (m + 2)) • hypF K m) (mid j) = 0
    rw [one_smul, hypF, Pi.single_eq_of_ne (mid_ne_rev_zero j)]
  map_mul' q₁ q₂ := by
    obtain ⟨v₁, c₁, hc₁, hq₁⟩ := q₁.2
    obtain ⟨v₂, c₂, hc₂, hq₂⟩ := q₂.2
    apply Multiplicative.toAdd.injective
    funext j
    change (((q₁ : SU σ (m + 2)) * (q₂ : SU σ (m + 2))) • hypF K m) (mid j) =
      ((q₁ : SU σ (m + 2)) • hypF K m) (mid j) + ((q₂ : SU σ (m + 2)) • hypF K m) (mid j)
    rw [hq₁, hq₂, heis_mul, heis_smul_hypF_mid, heis_smul_hypF_mid, heis_smul_hypF_mid,
      Pi.add_apply]

@[simp] theorem toAdd_heisProj_mkHeis (hσ : ∀ c, σ (σ c) = c) (v : Fin m → K) (c : K)
    (hc : c + σ c = -hermJ σ v v) :
    (heisProj hσ m (mkHeis hσ v c hc)).toAdd = v := by
  funext j
  exact heis_smul_hypF_mid hσ v c hc j

/-- Central subgroup `Z₀ = (heisProj hσ m).ker` of `heisSubgroup hσ m`. -/
noncomputable def heisCenter (hσ : ∀ c, σ (σ c) = c) (m : ℕ) : Subgroup (heisSubgroup hσ m) :=
  (heisProj hσ m).ker

theorem mem_heisCenter_iff (hσ : ∀ c, σ (σ c) = c) {q : heisSubgroup hσ m} :
    q ∈ heisCenter hσ m ↔ (heisProj hσ m q).toAdd = 0 := by
  rw [heisCenter, MonoidHom.mem_ker, ← toAdd_eq_zero]

theorem mkHeis_mem_heisCenter_iff (hσ : ∀ c, σ (σ c) = c) (v : Fin m → K) (c : K)
    (hc : c + σ c = -hermJ σ v v) :
    mkHeis hσ v c hc ∈ heisCenter hσ m ↔ v = 0 := by
  rw [mem_heisCenter_iff, toAdd_heisProj_mkHeis]

/-- Central element `mkHeis 0 c` with `c + σ c = 0`. -/
noncomputable def mkHeisZ (hσ : ∀ c, σ (σ c) = c) (c : K) (hc : c + σ c = 0) :
    heisSubgroup hσ m :=
  mkHeis hσ 0 c (by rw [hermJ_zero_left, neg_zero]; exact hc)

theorem mkHeisZ_mem_heisCenter (hσ : ∀ c, σ (σ c) = c) (c : K) (hc : c + σ c = 0) :
    mkHeisZ hσ c hc ∈ heisCenter hσ m :=
  (mkHeis_mem_heisCenter_iff hσ 0 c _).mpr rfl

theorem eq_mkHeisZ_of_mem_heisCenter (hσ : ∀ c, σ (σ c) = c) {q : heisSubgroup hσ m}
    (hq : q ∈ heisCenter hσ m) :
    ∃ (c : K) (hc : c + σ c = 0), q = mkHeisZ hσ c hc := by
  obtain ⟨v, c, hc, hq'⟩ := q.2
  have hq_eq : q = mkHeis hσ v c hc := Subtype.ext hq'
  rw [hq_eq, mkHeis_mem_heisCenter_iff] at hq
  subst hq
  have hc0 : c + σ c = 0 := by simpa using hc
  exact ⟨c, hc0, hq_eq⟩

theorem mkHeis_commutator (hσ : ∀ c, σ (σ c) = c) (v₁ v₂ : Fin m → K) (c₁ c₂ : K)
    (hc₁ : c₁ + σ c₁ = -hermJ σ v₁ v₁) (hc₂ : c₂ + σ c₂ = -hermJ σ v₂ v₂) :
    ⁅mkHeis hσ v₁ c₁ hc₁, mkHeis hσ v₂ c₂ hc₂⁆ =
      mkHeisZ hσ (hermJ σ v₂ v₁ - hermJ σ v₁ v₂) (by
        rw [map_sub, hermJ_conj' σ hσ v₂ v₁, hermJ_conj' σ hσ v₁ v₂]; ring) := by
  rw [commutatorElement_def, mkHeis_inv, mkHeis_inv, mkHeis_mul, mkHeis_mul, mkHeis_mul,
    mkHeisZ, mkHeis_ext_iff]
  refine ⟨by abel, ?_⟩
  simp only [hermJ_add_left, hermJ_neg_left, hermJ_neg_right]
  ring

theorem heisCenter_le_center (hσ : ∀ c, σ (σ c) = c) :
    heisCenter hσ m ≤ Subgroup.center (heisSubgroup hσ m) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨c, hc, rfl⟩ := eq_mkHeisZ_of_mem_heisCenter hσ hz
  obtain ⟨v, c', hc', hq⟩ := q.2
  have hq' : q = mkHeis hσ v c' hc' := Subtype.ext hq
  rw [hq', mkHeisZ, mkHeis_mul, mkHeis_mul, mkHeis_ext_iff]
  simp [add_comm]

theorem commutator_mem_heisCenter (hσ : ∀ c, σ (σ c) = c) (q₁ q₂ : heisSubgroup hσ m) :
    ⁅q₁, q₂⁆ ∈ heisCenter hσ m := by
  obtain ⟨v₁, c₁, hc₁, hq₁⟩ := q₁.2
  obtain ⟨v₂, c₂, hc₂, hq₂⟩ := q₂.2
  rw [show q₁ = mkHeis hσ v₁ c₁ hc₁ from Subtype.ext hq₁,
    show q₂ = mkHeis hσ v₂ c₂ hc₂ from Subtype.ext hq₂, mkHeis_commutator]
  exact mkHeisZ_mem_heisCenter hσ _ _

theorem pow_char_mem_heisCenter (hσ : ∀ c, σ (σ c) = c) (p : ℕ) [CharP K p]
    (q : heisSubgroup hσ m) : q ^ p ∈ heisCenter hσ m := by
  rw [mem_heisCenter_iff, map_pow, toAdd_pow]
  funext j
  simp [nsmul_eq_mul]

theorem heisProj_surjective (hσ : IsUnitaryInvolution σ) :
    Function.Surjective (heisProj hσ.invol m) := by
  intro v
  obtain ⟨c₀, hc₀⟩ := hσ.trace_surj (-hermJ σ v.toAdd v.toAdd)
    (by rw [map_neg, hermJ_self_fixed σ hσ.invol])
  refine ⟨mkHeis hσ.invol v.toAdd c₀ hc₀, ?_⟩
  rw [← ofAdd_toAdd (heisProj hσ.invol m _), toAdd_heisProj_mkHeis, ofAdd_toAdd]

theorem index_heisCenter (hσ : IsUnitaryInvolution σ) [Finite K] :
    (heisCenter hσ.invol m).index = (Nat.card K) ^ m := by
  classical
  have := Fintype.ofFinite K
  rw [heisCenter, Subgroup.index_ker,
    MonoidHom.range_eq_top_of_surjective _ (heisProj_surjective hσ),
    Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card]

theorem conj_heis_norm_aux (hσ : ∀ c, σ (σ c) = c) {g : SU σ (m + 2)} {κ : K}
    (hE : g • hypE K m = κ • hypE K m) (hF : g • hypF K m = (σ κ)⁻¹ • hypF K m)
    (v : Fin m → K) {c : K} (hc : c + σ c = -hermJ σ v v) :
    σ κ * κ * c + σ (σ κ * κ * c) =
      -hermJ σ (fun j => σ κ * (g • embMid v) (mid j))
        (fun j => σ κ * (g • embMid v) (mid j)) := by
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    have hE0 : g • hypE K m = 0 := by rw [hE, zero_smul]
    have h1 := hermJ_smul_smul σ g (hypE K m) (hypF K m)
    rw [hE0, hermJ_zero_left, hermJ_hypE_hypF] at h1
    exact zero_ne_one h1
  have hgy0 : (g • embMid v) 0 = 0 := by
    have := hermJ_smul_smul σ g (hypF K m) (embMid v)
    rw [hF, hermJ_smul_left, hermJ_hypF_left, hermJ_hypF_embMid, map_inv₀, hσ] at this
    exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero hκ0)
  have hgy1 : (g • embMid v) (Fin.rev 0) = 0 := by
    have := hermJ_smul_smul σ g (hypE K m) (embMid v)
    rw [hE, hermJ_smul_left, hermJ_hypE_left, hermJ_hypE_embMid] at this
    exact (mul_eq_zero.mp this).resolve_left ((map_ne_zero σ).mpr hκ0)
  have hemb : embMid (fun j => σ κ * (g • embMid v) (mid j)) = σ κ • (g • embMid v) := by
    have h1 : (fun j => σ κ * (g • embMid v) (mid j)) =
        σ κ • fun j => (g • embMid v) (mid j) := rfl
    rw [h1, embMid_smul, embMid_eq_of_zero hgy0 hgy1]
  have hnorm : hermJ σ (fun j => σ κ * (g • embMid v) (mid j))
      (fun j => σ κ * (g • embMid v) (mid j)) = σ κ * κ * hermJ σ v v := by
    rw [← hermJ_embMid_embMid, hemb, hermJ_smul_left, hermJ_smul_right, hσ,
      hermJ_smul_smul, hermJ_embMid_embMid]
    ring
  rw [hnorm, map_mul, map_mul, hσ]
  linear_combination (σ κ * κ) * hc

/-- Any `g : SU σ (m + 2)` that scales `hypE K m` by `κ` and `hypF K m` by `(σ κ)⁻¹` conjugates
`heis hσ v c hc` to `heis hσ v' ((σ κ * κ) * c)` where `v' j = σ κ * (g • embMid v) (mid j)`. -/
theorem conj_heis_of_smul_hyp (hσ : ∀ c, σ (σ c) = c) {g : SU σ (m + 2)} {κ : K}
    (hE : g • hypE K m = κ • hypE K m) (hF : g • hypF K m = (σ κ)⁻¹ • hypF K m)
    (v : Fin m → K) (c : K) (hc : c + σ c = -hermJ σ v v) :
    g * heis hσ v c hc * g⁻¹ =
      heis hσ (fun j => σ κ * (g • embMid v) (mid j)) (σ κ * κ * c)
        (conj_heis_norm_aux hσ hE hF v hc) := by
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    have hE0 : g • hypE K m = 0 := by rw [hE, zero_smul]
    have h1 := hermJ_smul_smul σ g (hypE K m) (hypF K m)
    rw [hE0, hermJ_zero_left, hermJ_hypE_hypF] at h1
    exact zero_ne_one h1
  have hgy0 : (g • embMid v) 0 = 0 := by
    have := hermJ_smul_smul σ g (hypF K m) (embMid v)
    rw [hF, hermJ_smul_left, hermJ_hypF_left, hermJ_hypF_embMid, map_inv₀, hσ] at this
    exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero hκ0)
  have hgy1 : (g • embMid v) (Fin.rev 0) = 0 := by
    have := hermJ_smul_smul σ g (hypE K m) (embMid v)
    rw [hE, hermJ_smul_left, hermJ_hypE_left, hermJ_hypE_embMid] at this
    exact (mul_eq_zero.mp this).resolve_left ((map_ne_zero σ).mpr hκ0)
  have hemb : embMid (fun j => σ κ * (g • embMid v) (mid j)) = σ κ • (g • embMid v) := by
    have h1 : (fun j => σ κ * (g • embMid v) (mid j)) =
        σ κ • fun j => (g • embMid v) (mid j) := rfl
    rw [h1, embMid_smul, embMid_eq_of_zero hgy0 hgy1]
  apply ext_smul_SU
  intro x
  rw [mul_smul, mul_smul, heis_smul, smul_sub, smul_add, smul_inv_smul,
    smul_comm g (hermJ σ (hypE K m) (g⁻¹ • x)), smul_comm g (hermJ σ (embMid v) (g⁻¹ • x)),
    smul_add, smul_comm g c, hE,
    ← hermJ_smul_smul σ g (hypE K m) (g⁻¹ • x), ← hermJ_smul_smul σ g (embMid v) (g⁻¹ • x),
    smul_inv_smul, hE, hermJ_smul_left, heis_smul, hemb, hermJ_smul_left, hσ]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Any `g : SU σ (m + 2)` scaling `hypE K m` by `κ` and `hypF K m` by `(σ κ)⁻¹` normalizes
`heisSubgroup hσ m`. -/
theorem mem_normalizer_heisSubgroup_of_smul_hyp (hσ : ∀ c, σ (σ c) = c) {g : SU σ (m + 2)}
    {κ : K} (hE : g • hypE K m = κ • hypE K m) (hF : g • hypF K m = (σ κ)⁻¹ • hypF K m) :
    g ∈ Subgroup.normalizer (heisSubgroup hσ m : Set (SU σ (m + 2))) := by
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    have hE0 : g • hypE K m = 0 := by rw [hE, zero_smul]
    have h1 := hermJ_smul_smul σ g (hypE K m) (hypF K m)
    rw [hE0, hermJ_zero_left, hermJ_hypE_hypF] at h1
    exact zero_ne_one h1
  have hE' : g⁻¹ • hypE K m = κ⁻¹ • hypE K m := by
    rw [inv_smul_eq_iff, smul_comm, hE, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
  have hF' : g⁻¹ • hypF K m = (σ κ⁻¹)⁻¹ • hypF K m := by
    rw [map_inv₀, inv_inv, inv_smul_eq_iff, smul_comm, hF, smul_smul,
      mul_inv_cancel₀ ((map_ne_zero σ).mpr hκ0), one_smul]
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · rintro ⟨v, c, hc, rfl⟩
    exact ⟨_, _, _, conj_heis_of_smul_hyp hσ hE hF v c hc⟩
  · intro ⟨v, c, hc, hq⟩
    have := conj_heis_of_smul_hyp hσ hE' hF' v c hc
    rw [inv_inv, ← hq] at this
    have heq : q = g⁻¹ * (g * q * g⁻¹) * g := by group
    exact ⟨_, _, _, heq.trans this⟩

theorem diagSU_smul_hypE (t : Fin (m + 2) → K) (hdet : ∏ i, t i = 1)
    (hiso : ∀ i, σ (t i) * t (Fin.rev i) = 1) :
    diagSU t hdet hiso • hypE K m = t 0 • hypE K m := by
  funext i
  rw [diagSU_smul_apply, Pi.smul_apply, smul_eq_mul, hypE]
  by_cases hi : i = 0
  · subst hi; simp
  · rw [Pi.single_eq_of_ne hi, mul_zero, mul_zero]

theorem diagSU_smul_hypF (t : Fin (m + 2) → K) (hdet : ∏ i, t i = 1)
    (hiso : ∀ i, σ (t i) * t (Fin.rev i) = 1) :
    diagSU t hdet hiso • hypF K m = (σ (t 0))⁻¹ • hypF K m := by
  have ht1 : t (Fin.rev 0) = (σ (t 0))⁻¹ := eq_inv_of_mul_eq_one_right (hiso 0)
  funext i
  rw [diagSU_smul_apply, Pi.smul_apply, smul_eq_mul, hypF]
  by_cases hi : i = Fin.rev 0
  · subst hi; rw [ht1]
  · rw [Pi.single_eq_of_ne hi, mul_zero, mul_zero]

/-- Any diagonal matrix `diagSU t hdet hiso` in `SU σ (m + 2)` normalizes `heisSubgroup hσ m`. -/
theorem diagSU_mem_normalizer_heisSubgroup (hσ : ∀ c, σ (σ c) = c) (t : Fin (m + 2) → K)
    (hdet : ∏ i, t i = 1) (hiso : ∀ i, σ (t i) * t (Fin.rev i) = 1) :
    diagSU t hdet hiso ∈ Subgroup.normalizer (heisSubgroup hσ m : Set (SU σ (m + 2))) :=
  mem_normalizer_heisSubgroup_of_smul_hyp hσ
    (diagSU_smul_hypE t hdet hiso) (diagSU_smul_hypF t hdet hiso)

/-- Conjugation of `heis hσ v c hc` by `diagSU t hdet hiso`. -/
theorem conj_diagSU_heis (hσ : ∀ c, σ (σ c) = c) (t : Fin (m + 2) → K)
    (hdet : ∏ i, t i = 1) (hiso : ∀ i, σ (t i) * t (Fin.rev i) = 1)
    (v : Fin m → K) (c : K) (hc : c + σ c = -hermJ σ v v) :
    diagSU t hdet hiso * heis hσ v c hc * (diagSU t hdet hiso)⁻¹ =
      heis hσ (fun j => σ (t 0) * t (mid j) * v j) (σ (t 0) * t 0 * c) (by
        have hE := diagSU_smul_hypE t hdet hiso
        have hF := diagSU_smul_hypF t hdet hiso
        have hvec : (fun j => σ (t 0) * (diagSU t hdet hiso • embMid v) (mid j)) =
            fun j => σ (t 0) * t (mid j) * v j := by
          funext j
          rw [diagSU_smul_apply, embMid_mid, mul_assoc]
        rw [← hvec]
        exact conj_heis_norm_aux hσ hE hF v hc) := by
  have hE := diagSU_smul_hypE t hdet hiso
  have hF := diagSU_smul_hypF t hdet hiso
  rw [conj_heis_of_smul_hyp hσ hE hF v c hc]
  congr 1
  funext j
  rw [diagSU_smul_apply, embMid_mid, mul_assoc]

theorem hermJ_single_mid_self {j : Fin m} (hj : Fin.rev j ≠ j) :
    hermJ σ (Pi.single (mid j) (1 : K)) (Pi.single (mid j) 1) = 0 := by
  rw [hermJ_single_left, map_one, one_mul, rev_mid,
    Pi.single_eq_of_ne (fun h => hj (mid_injective h))]

/-- Middle long-root transvection `tvJ` along `Pi.single (mid j) 1` when `Fin.rev j ≠ j`. -/
noncomputable def midRoot (hσ : ∀ c, σ (σ c) = c) {j : Fin m} (hj : Fin.rev j ≠ j)
    (τ : K) (hτ : τ + σ τ = 0) : SU σ (m + 2) :=
  tvJ hσ (hermJ_single_mid_self hj) τ hτ

theorem midRoot_smul_hypE (hσ : ∀ c, σ (σ c) = c) {j : Fin m} (hj : Fin.rev j ≠ j)
    (τ : K) (hτ : τ + σ τ = 0) :
    midRoot hσ hj τ hτ • hypE K m = (1 : K) • hypE K m := by
  rw [midRoot, tvJ_smul, hermJ_single_left, rev_mid, hypE,
    Pi.single_eq_of_ne (mid_ne_zero (Fin.rev j)), mul_zero, mul_zero, zero_smul,
    add_zero, one_smul]

theorem midRoot_smul_hypF (hσ : ∀ c, σ (σ c) = c) {j : Fin m} (hj : Fin.rev j ≠ j)
    (τ : K) (hτ : τ + σ τ = 0) :
    midRoot hσ hj τ hτ • hypF K m = (σ (1 : K))⁻¹ • hypF K m := by
  rw [midRoot, tvJ_smul, hermJ_single_left, rev_mid, hypF,
    Pi.single_eq_of_ne (mid_ne_rev_zero (Fin.rev j)), mul_zero, mul_zero, zero_smul,
    add_zero, map_one, inv_one, one_smul]

theorem midRoot_mem_normalizer_heisSubgroup (hσ : ∀ c, σ (σ c) = c) {j : Fin m}
    (hj : Fin.rev j ≠ j) (τ : K) (hτ : τ + σ τ = 0) :
    midRoot hσ hj τ hτ ∈ Subgroup.normalizer (heisSubgroup hσ m : Set (SU σ (m + 2))) :=
  mem_normalizer_heisSubgroup_of_smul_hyp hσ
    (midRoot_smul_hypE hσ hj τ hτ) (midRoot_smul_hypF hσ hj τ hτ)

theorem conj_midRoot_heis (hσ : ∀ c, σ (σ c) = c) {j : Fin m} (hj : Fin.rev j ≠ j)
    (τ : K) (hτ : τ + σ τ = 0) (v : Fin m → K) (c : K) (hc : c + σ c = -hermJ σ v v) :
    midRoot hσ hj τ hτ * heis hσ v c hc * (midRoot hσ hj τ hτ)⁻¹ =
      heis hσ (v + Pi.single j (τ * v (Fin.rev j))) c (by
        have hE := midRoot_smul_hypE hσ hj τ hτ
        have hF := midRoot_smul_hypF hσ hj τ hτ
        have hvec : (fun k => σ (1 : K) * (midRoot hσ hj τ hτ • embMid v) (mid k)) =
            v + Pi.single j (τ * v (Fin.rev j)) := by
          funext k
          rw [map_one, one_mul, midRoot, tvJ_smul, hermJ_single_left, rev_mid, map_one, one_mul,
            Pi.add_apply, embMid_mid, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
          by_cases hkj : k = j
          · subst hkj; simp
          · have hk' : mid k ≠ mid j := fun h => hkj (mid_injective h)
            simp [Pi.single_eq_of_ne hkj, Pi.single_eq_of_ne hk']
        have hc' : σ (1 : K) * 1 * c = c := by rw [map_one, one_mul, one_mul]
        rw [← hvec, ← hc']
        exact conj_heis_norm_aux hσ hE hF v hc) := by
  have hE := midRoot_smul_hypE hσ hj τ hτ
  have hF := midRoot_smul_hypF hσ hj τ hτ
  rw [conj_heis_of_smul_hyp hσ hE hF v c hc]
  congr 1
  · funext k
    rw [map_one, one_mul, midRoot, tvJ_smul, hermJ_single_left, rev_mid, map_one, one_mul,
      Pi.add_apply, embMid_mid, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    by_cases hkj : k = j
    · subst hkj; simp
    · have hk' : mid k ≠ mid j := fun h => hkj (mid_injective h)
      simp [Pi.single_eq_of_ne hkj, Pi.single_eq_of_ne hk']
  · rw [map_one, one_mul, one_mul]

end HeisenbergSubgroup

end Maroti.Unitary
