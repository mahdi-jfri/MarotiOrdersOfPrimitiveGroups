module

public import Maroti.MinDegree.Heisenberg
public import Maroti.Classical.SymplecticOrderBound
public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.ClassicalGroups.Symplectic.Simple

/-!
# Point-Radical Heisenberg Subgroups and Maróti's Theorem for `PSp(2n, q)` in Odd Characteristic

This file proves the subgroup index lower bound `p * (p ^ f) ^ (2 * n - 2) ≤ H.index` for every
proper subgroup `H` of `PSp(2n, p^f)` in odd characteristic
(`Maroti.index_ge_of_statedClassicalModel_psp_odd`) and deduces `Maroti.symplecticCase_odd`
(Maróti, Section 2, Step 2, page 634). For comparison, the exact minimal degree is given in
Kleidman and Liebeck, *The Subgroup Structure of the Finite Classical Groups*, Table 5.2.A,
page 175.

For `n = m + 1 ≥ 2` and a finite field `K` of odd characteristic `p` with `|K| = q = p^f`, the point
radical `Q` of the isotropic basis vector `e₀ = inl 0` in `Sp(2m + 2, K)` consists of the Siegel
transformations
`spHeis w c = siegel (spForm (m + 1) K) spForm_isAlt e₀ (embSpVec w) c`
(`CFSG/ClassicalGroups/Symplectic/StandardForm.lean`) for `w : Fin m ⊕ Fin m → K` and `c : K`.
Its multiplication law is
`spHeis w₁ c₁ * spHeis w₂ c₂ = spHeis (w₁ + w₂) (c₁ + c₂ + spForm m K w₂ w₁)`
and its commutator law is
`⁅spHeis w₁ c₁, spHeis w₂ c₂⁆ = spHeis 0 (2 * spForm m K w₂ w₁)`.

The center `Z(Q) = { spHeis 0 c | c : K }` has order `q` and index `q^(2m) = q^(2n - 2)` in `Q`.
Because `(2 : K) ≠ 0` and `spForm m K` is nondegenerate, the commutator map is surjective onto
`Z(Q)` for every `x ∈ Q \ Z(Q)`. Moreover, the Levi subgroup `Sp(2m, K)` embeds into
`N_{Sp(2m + 2, K)}(Q)` via `extGsp`, acting on `spHeis w c` by `spHeis (g.app w) c`. Since
`Sp(2m, K)` acts transitively on the nonzero vectors of `Fin m ⊕ Fin m → K` (`exists_gsp_apply_eq`),
`N_{Sp(2m + 2, K)}(Q)` acts transitively on `Q \ Z(Q)` up to `Z(Q)`.

Applying `Maroti.mul_index_center_le_index_of_map_ne_bot_of_ne_top` and simplicity of `PSp(2n, p^f)`
(`CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp` in
`CFSG/ClassicalGroups/Symplectic/Simple.lean`) gives the minimum subgroup index bound
`p * (p ^ f) ^ (2 * n - 2) ≤ H.index` for every proper subgroup `H` of `PSp(2n, p^f)` with `p ≠ 2`.
Combining this with `Maroti.card_mul_outer_le_bound_psp_odd` and `Maroti.card_outerAut_psp_dvd`
proves `Maroti.symplecticCase_odd`.
-/

@[expose] public section

namespace Maroti

open CFSG.Open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement

namespace SymplecticHeisenberg

variable {m : ℕ} {K : Type} [Field K]

/-! ### Coordinates and hyperbolic splitting on `Fin (m + 1) ⊕ Fin (m + 1) → K` -/

/-- First isotropic basis vector `e₀ = inl 0` in `Fin (m + 1) ⊕ Fin (m + 1) → K`. -/
def spE0 (m : ℕ) (K : Type) [Field K] : Fin (m + 1) ⊕ Fin (m + 1) → K :=
  Pi.single (Sum.inl 0) 1

/-- Hyperbolic partner `f₀ = inr 0` of `spE0 m K` in `Fin (m + 1) ⊕ Fin (m + 1) → K`. -/
def spF0 (m : ℕ) (K : Type) [Field K] : Fin (m + 1) ⊕ Fin (m + 1) → K :=
  Pi.single (Sum.inr 0) 1

/-- Embedding of `Fin m ⊕ Fin m → K` into `Fin (m + 1) ⊕ Fin (m + 1) → K` on the `Fin.succ`
coordinates (with `0` on `inl 0` and `inr 0`). -/
def embSpVec (w : Fin m ⊕ Fin m → K) : Fin (m + 1) ⊕ Fin (m + 1) → K :=
  Sum.elim (Fin.cases 0 (fun j => w (Sum.inl j))) (Fin.cases 0 (fun j => w (Sum.inr j)))

/-- Projection of `Fin (m + 1) ⊕ Fin (m + 1) → K` onto the `Fin.succ` coordinates. -/
def projSpVec (x : Fin (m + 1) ⊕ Fin (m + 1) → K) : Fin m ⊕ Fin m → K :=
  Sum.elim (fun j => x (Sum.inl j.succ)) (fun j => x (Sum.inr j.succ))

@[simp] theorem spE0_inl_zero : spE0 m K (Sum.inl 0) = 1 := by simp [spE0]
@[simp] theorem spE0_inr_zero : spE0 m K (Sum.inr 0) = 0 := by simp [spE0]
@[simp] theorem spF0_inl_zero : spF0 m K (Sum.inl 0) = 0 := by simp [spF0]
@[simp] theorem spF0_inr_zero : spF0 m K (Sum.inr 0) = 1 := by simp [spF0]

@[simp] theorem embSpVec_inl_zero (w : Fin m ⊕ Fin m → K) :
    embSpVec w (Sum.inl 0) = 0 := rfl

@[simp] theorem embSpVec_inr_zero (w : Fin m ⊕ Fin m → K) :
    embSpVec w (Sum.inr 0) = 0 := rfl

@[simp] theorem embSpVec_inl_succ (w : Fin m ⊕ Fin m → K) (j : Fin m) :
    embSpVec w (Sum.inl j.succ) = w (Sum.inl j) := rfl

@[simp] theorem embSpVec_inr_succ (w : Fin m ⊕ Fin m → K) (j : Fin m) :
    embSpVec w (Sum.inr j.succ) = w (Sum.inr j) := rfl

@[simp] theorem projSpVec_embSpVec (w : Fin m ⊕ Fin m → K) :
    projSpVec (embSpVec w) = w := by
  ext k
  rcases k with j | j <;> rfl

theorem embSpVec_injective : Function.Injective (embSpVec (m := m) (K := K)) :=
  Function.LeftInverse.injective projSpVec_embSpVec

@[simp] theorem projSpVec_spE0 : projSpVec (spE0 m K) = 0 := by
  ext k
  rcases k with j | j <;> simp [projSpVec, spE0]

@[simp] theorem projSpVec_spF0 : projSpVec (spF0 m K) = 0 := by
  ext k
  rcases k with j | j <;> simp [projSpVec, spF0]

@[simp] theorem projSpVec_zero : projSpVec (0 : Fin (m + 1) ⊕ Fin (m + 1) → K) = 0 := by
  ext k; rcases k with j | j <;> rfl

theorem projSpVec_add (x y : Fin (m + 1) ⊕ Fin (m + 1) → K) :
    projSpVec (x + y) = projSpVec x + projSpVec y := by
  ext k; rcases k with j | j <;> rfl

theorem projSpVec_sub (x y : Fin (m + 1) ⊕ Fin (m + 1) → K) :
    projSpVec (x - y) = projSpVec x - projSpVec y := by
  ext k; rcases k with j | j <;> rfl

theorem projSpVec_smul (c : K) (x : Fin (m + 1) ⊕ Fin (m + 1) → K) :
    projSpVec (c • x) = c • projSpVec x := by
  ext k; rcases k with j | j <;> rfl

@[simp] theorem embSpVec_zero : embSpVec (0 : Fin m ⊕ Fin m → K) = 0 := by
  ext k
  rcases k with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem embSpVec_add (w₁ w₂ : Fin m ⊕ Fin m → K) :
    embSpVec (w₁ + w₂) = embSpVec w₁ + embSpVec w₂ := by
  ext k
  rcases k with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [embSpVec]

theorem embSpVec_neg (w : Fin m ⊕ Fin m → K) :
    embSpVec (-w) = -embSpVec w := by
  ext k
  rcases k with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [embSpVec]

theorem embSpVec_smul (c : K) (w : Fin m ⊕ Fin m → K) :
    embSpVec (c • w) = c • embSpVec w := by
  ext k
  rcases k with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [embSpVec]

theorem embSpVec_nsmul (k : ℕ) (w : Fin m ⊕ Fin m → K) :
    embSpVec (k • w) = k • embSpVec w := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, succ_nsmul, embSpVec_add, ih]

/-- Recursive formula for `spForm (m + 1) K` splitting off the `(inl 0, inr 0)` hyperbolic pair. -/
theorem spForm_succ_eq (x y : Fin (m + 1) ⊕ Fin (m + 1) → K) :
    spForm (m + 1) K x y =
      (x (Sum.inl 0) * y (Sum.inr 0) - x (Sum.inr 0) * y (Sum.inl 0)) +
        spForm m K (projSpVec x) (projSpVec y) := by
  rw [spForm_apply, spForm_apply]
  simp only [dotProduct, Fintype.sum_sum_type, spJ_mulVec_inl, spJ_mulVec_inr,
    Fin.sum_univ_succ, projSpVec, Sum.elim_inl, Sum.elim_inr]
  ring

@[simp] theorem spForm_spE0_left (x : Fin (m + 1) ⊕ Fin (m + 1) → K) :
    spForm (m + 1) K (spE0 m K) x = x (Sum.inr 0) := by
  rw [spForm_succ_eq]
  simp

@[simp] theorem spForm_spE0_right (x : Fin (m + 1) ⊕ Fin (m + 1) → K) :
    spForm (m + 1) K x (spE0 m K) = -x (Sum.inr 0) := by
  rw [spForm_succ_eq]
  simp

@[simp] theorem spForm_spF0_left (x : Fin (m + 1) ⊕ Fin (m + 1) → K) :
    spForm (m + 1) K (spF0 m K) x = -x (Sum.inl 0) := by
  rw [spForm_succ_eq]
  simp

@[simp] theorem spForm_spF0_right (x : Fin (m + 1) ⊕ Fin (m + 1) → K) :
    spForm (m + 1) K x (spF0 m K) = x (Sum.inl 0) := by
  rw [spForm_succ_eq]
  simp

@[simp] theorem spForm_embSpVec (w₁ w₂ : Fin m ⊕ Fin m → K) :
    spForm (m + 1) K (embSpVec w₁) (embSpVec w₂) = spForm m K w₁ w₂ := by
  rw [spForm_succ_eq]
  simp

theorem spForm_swap (w₁ w₂ : Fin m ⊕ Fin m → K) :
    spForm m K w₁ w₂ = -spForm m K w₂ w₁ :=
  (spForm_isAlt.neg_eq w₂ w₁).symm

/-! ### Levi embedding `extGsp : Gsp (spForm m K) →* Gsp (spForm (m + 1) K)` -/

/-- Extension of a linear map on `Fin m ⊕ Fin m → K` to `Fin (m + 1) ⊕ Fin (m + 1) → K` acting
as the identity on `spE0` and `spF0`. -/
def extSpLin (f : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) :
    (Fin (m + 1) ⊕ Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K) where
  toFun x := Sum.elim
    (Fin.cases (x (Sum.inl 0)) (fun j => f (projSpVec x) (Sum.inl j)))
    (Fin.cases (x (Sum.inr 0)) (fun j => f (projSpVec x) (Sum.inr j)))
  map_add' x y := by
    ext k
    rcases k with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [projSpVec_add]
  map_smul' c x := by
    ext k
    rcases k with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [projSpVec_smul]

@[simp] theorem extSpLin_inl_zero (f : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K))
    (x : Fin (m + 1) ⊕ Fin (m + 1) → K) :
    extSpLin f x (Sum.inl 0) = x (Sum.inl 0) := rfl

@[simp] theorem extSpLin_inr_zero (f : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K))
    (x : Fin (m + 1) ⊕ Fin (m + 1) → K) :
    extSpLin f x (Sum.inr 0) = x (Sum.inr 0) := rfl

@[simp] theorem projSpVec_extSpLin (f : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K))
    (x : Fin (m + 1) ⊕ Fin (m + 1) → K) :
    projSpVec (extSpLin f x) = f (projSpVec x) := by
  ext k
  rcases k with j | j <;> rfl

@[simp] theorem extSpLin_id :
    extSpLin (LinearMap.id : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) = LinearMap.id := by
  refine LinearMap.ext fun x => funext fun k => ?_
  rcases k with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem extSpLin_comp (f₁ f₂ : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) :
    (extSpLin f₁).comp (extSpLin f₂) = extSpLin (f₁.comp f₂) := by
  refine LinearMap.ext fun x => funext fun k => ?_
  rcases k with i | i <;> refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change f₁ (projSpVec (extSpLin f₂ x)) (Sum.inl j) = f₁ (f₂ (projSpVec x)) (Sum.inl j)
    rw [projSpVec_extSpLin]
  · rfl
  · change f₁ (projSpVec (extSpLin f₂ x)) (Sum.inr j) = f₁ (f₂ (projSpVec x)) (Sum.inr j)
    rw [projSpVec_extSpLin]

@[simp] theorem extSpLin_spE0 (f : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) :
    extSpLin f (spE0 m K) = spE0 m K := by
  ext k
  rcases k with i | i <;> refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change f (projSpVec (spE0 m K)) (Sum.inl j) = spE0 m K (Sum.inl j.succ)
    rw [projSpVec_spE0, map_zero]
    simp [spE0]
  · rfl
  · change f (projSpVec (spE0 m K)) (Sum.inr j) = spE0 m K (Sum.inr j.succ)
    rw [projSpVec_spE0, map_zero]
    simp [spE0]

@[simp] theorem extSpLin_embSpVec (f : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K))
    (w : Fin m ⊕ Fin m → K) :
    extSpLin f (embSpVec w) = embSpVec (f w) := by
  ext k
  rcases k with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [extSpLin]

/-- Extension of an isometry `g : Gsp (spForm m K)` to `Gsp (spForm (m + 1) K)`. -/
noncomputable def extGsp (g : Gsp (spForm m K)) : Gsp (spForm (m + 1) K) :=
  ⟨{ val := extSpLin (g : LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K))
     inv := extSpLin ((g⁻¹ : Gsp (spForm m K)) :
       LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K))
     val_inv := by
       change (extSpLin _).comp (extSpLin _) = LinearMap.id
       rw [extSpLin_comp]
       have h : ((g : LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) :
           (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)).comp
         (((g⁻¹ : Gsp (spForm m K)) : LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) :
           (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) = LinearMap.id :=
         (g : LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)).val_inv
       rw [h, extSpLin_id]
     inv_val := by
       change (extSpLin _).comp (extSpLin _) = LinearMap.id
       rw [extSpLin_comp]
       have h : (((g⁻¹ : Gsp (spForm m K)) :
           LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) :
           (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)).comp
         ((g : LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) :
           (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) = LinearMap.id :=
         (g : LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)).inv_val
       rw [h, extSpLin_id] },
   fun x y => by
     show spForm (m + 1) K (extSpLin _ x) (extSpLin _ y) = spForm (m + 1) K x y
     rw [spForm_succ_eq, spForm_succ_eq (x := x) (y := y), extSpLin_inl_zero, extSpLin_inr_zero,
       extSpLin_inl_zero, extSpLin_inr_zero, projSpVec_extSpLin, projSpVec_extSpLin]
     exact congrArg (_ + ·) (g.form_app (projSpVec x) (projSpVec y))⟩

@[simp] theorem extGsp_app_spE0 (g : Gsp (spForm m K)) :
    (extGsp g).app (spE0 m K) = spE0 m K :=
  extSpLin_spE0 _

@[simp] theorem extGsp_app_embSpVec (g : Gsp (spForm m K)) (w : Fin m ⊕ Fin m → K) :
    (extGsp g).app (embSpVec w) = embSpVec (g.app w) :=
  extSpLin_embSpVec _ w

/-! ### Siegel Heisenberg elements `spHeis w c` -/

/-- The Siegel transformation in `Gsp (spForm (m + 1) K)` parameterized by `w : Fin m ⊕ Fin m → K`
and `c : K`. -/
noncomputable def spHeis (w : Fin m ⊕ Fin m → K) (c : K) : Gsp (spForm (m + 1) K) :=
  ⟨siegel (spForm (m + 1) K) spForm_isAlt (spE0 m K) (embSpVec w) c,
   siegel_mem_bilinIsometryGroup spForm_isAlt (spE0 m K) (embSpVec w) c⟩

theorem spHeis_app (w : Fin m ⊕ Fin m → K) (c : K) (x : Fin (m + 1) ⊕ Fin (m + 1) → K) :
    (spHeis w c).app x =
      x + spForm (m + 1) K x (spE0 m K) • embSpVec w +
        spForm (m + 1) K x (embSpVec w) • spE0 m K +
          (c * spForm (m + 1) K x (spE0 m K)) • spE0 m K :=
  siegel_apply spForm_isAlt (by simp) c x

@[simp] theorem spHeis_app_spE0 (w : Fin m ⊕ Fin m → K) (c : K) :
    (spHeis w c).app (spE0 m K) = spE0 m K := by
  rw [spHeis_app]
  simp

theorem spHeis_app_spF0 (w : Fin m ⊕ Fin m → K) (c : K) :
    (spHeis w c).app (spF0 m K) = spF0 m K - embSpVec w - c • spE0 m K := by
  rw [spHeis_app, spForm_spE0_right, spForm_spF0_left]
  simp only [spF0_inr_zero, embSpVec_inl_zero, neg_zero, zero_smul, add_zero, mul_neg, mul_one,
    neg_smul, one_smul, sub_eq_add_neg]

@[simp] theorem spHeis_zero_zero : spHeis (0 : Fin m ⊕ Fin m → K) (0 : K) = 1 := by
  apply Subtype.ext
  change siegel (spForm (m + 1) K) spForm_isAlt (spE0 m K) (embSpVec 0) 0 = 1
  rw [embSpVec_zero, siegel_zero]

theorem spHeis_mul (w₁ w₂ : Fin m ⊕ Fin m → K) (c₁ c₂ : K) :
    spHeis w₁ c₁ * spHeis w₂ c₂ = spHeis (w₁ + w₂) (c₁ + c₂ + spForm m K w₂ w₁) := by
  apply Subtype.ext
  change siegel (spForm (m + 1) K) spForm_isAlt (spE0 m K) (embSpVec w₁) c₁ *
      siegel (spForm (m + 1) K) spForm_isAlt (spE0 m K) (embSpVec w₂) c₂ =
    siegel (spForm (m + 1) K) spForm_isAlt (spE0 m K) (embSpVec (w₁ + w₂))
      (c₁ + c₂ + spForm m K w₂ w₁)
  rw [siegel_mul spForm_isAlt (by simp) (by simp), embSpVec_add, spForm_embSpVec]

theorem spHeis_inv (w : Fin m ⊕ Fin m → K) (c : K) :
    (spHeis w c)⁻¹ = spHeis (-w) (-c) := by
  apply Subtype.ext
  change (siegel (spForm (m + 1) K) spForm_isAlt (spE0 m K) (embSpVec w) c)⁻¹ =
    siegel (spForm (m + 1) K) spForm_isAlt (spE0 m K) (embSpVec (-w)) (-c)
  rw [siegel_inv spForm_isAlt (by simp), embSpVec_neg]

theorem spHeis_comm (w₁ w₂ : Fin m ⊕ Fin m → K) (c₁ c₂ : K) :
    ⁅spHeis w₁ c₁, spHeis w₂ c₂⁆ = spHeis 0 (2 * spForm m K w₂ w₁) := by
  rw [commutatorElement_def, spHeis_inv, spHeis_inv, spHeis_mul, spHeis_mul, spHeis_mul]
  have hw : w₁ + w₂ + -w₁ + -w₂ = 0 := by abel
  have hw1 : w₁ + w₂ + -w₁ = w₂ := by abel
  rw [hw, hw1]
  simp only [map_add, map_neg, LinearMap.neg_apply, spForm_self, spForm_swap w₁ w₂]
  congr 1
  ring

theorem spHeis_eq_iff {w₁ w₂ : Fin m ⊕ Fin m → K} {c₁ c₂ : K} :
    spHeis w₁ c₁ = spHeis w₂ c₂ ↔ w₁ = w₂ ∧ c₁ = c₂ := by
  constructor
  · intro h
    have hf := congrArg (fun g : Gsp (spForm (m + 1) K) => g.app (spF0 m K)) h
    rw [spHeis_app_spF0, spHeis_app_spF0] at hf
    have hc : c₁ = c₂ := by
      have h0 := congrFun hf (Sum.inl 0)
      simp only [Pi.sub_apply, Pi.smul_apply, spF0_inl_zero, embSpVec_inl_zero, spE0_inl_zero,
        sub_zero, smul_eq_mul, mul_one, zero_sub, neg_inj] at h0
      exact h0
    have hw : w₁ = w₂ := by
      have hp := congrArg projSpVec hf
      simp only [projSpVec_sub, projSpVec_spF0, projSpVec_embSpVec, projSpVec_smul,
        projSpVec_spE0, smul_zero, sub_zero, zero_sub, neg_inj] at hp
      exact hp
    exact ⟨hw, hc⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem spHeis_injective :
    Function.Injective (fun p : (Fin m ⊕ Fin m → K) × K => spHeis p.1 p.2) := by
  rintro ⟨w₁, c₁⟩ ⟨w₂, c₂⟩ h
  obtain ⟨rfl, rfl⟩ := spHeis_eq_iff.mp h
  rfl

theorem extGsp_conj_spHeis (g : Gsp (spForm m K)) (w : Fin m ⊕ Fin m → K) (c : K) :
    extGsp g * spHeis w c * (extGsp g)⁻¹ = spHeis (g.app w) c := by
  apply Subtype.ext
  change (extGsp g : LinearMap.GeneralLinearGroup K _) *
      siegel (spForm (m + 1) K) spForm_isAlt (spE0 m K) (embSpVec w) c *
      (extGsp g : LinearMap.GeneralLinearGroup K _)⁻¹ =
    siegel (spForm (m + 1) K) spForm_isAlt (spE0 m K) (embSpVec (g.app w)) c
  rw [siegel_conj spForm_isAlt (extGsp g).2]
  change siegel (spForm (m + 1) K) spForm_isAlt ((extGsp g).app (spE0 m K))
      ((extGsp g).app (embSpVec w)) c = _
  rw [extGsp_app_spE0, extGsp_app_embSpVec]

/-! ### The Heisenberg subgroup `spHeisSubgroup` and its normalizer `spHeisNorm` -/

/-- The point-radical Heisenberg subgroup of `Gsp (spForm (m + 1) K)`. -/
def spHeisSubgroup (m : ℕ) (K : Type) [Field K] : Subgroup (Gsp (spForm (m + 1) K)) where
  carrier := { g | ∃ w c, spHeis w c = g }
  one_mem' := ⟨0, 0, spHeis_zero_zero⟩
  mul_mem' := by
    rintro _ _ ⟨w₁, c₁, rfl⟩ ⟨w₂, c₂, rfl⟩
    exact ⟨w₁ + w₂, c₁ + c₂ + spForm m K w₂ w₁, (spHeis_mul w₁ w₂ c₁ c₂).symm⟩
  inv_mem' := by
    rintro _ ⟨w, c, rfl⟩
    exact ⟨-w, -c, (spHeis_inv w c).symm⟩

/-- The normalizer of `spHeisSubgroup m K` in `Gsp (spForm (m + 1) K)`. -/
noncomputable def spHeisNorm (m : ℕ) (K : Type) [Field K] : Subgroup (Gsp (spForm (m + 1) K)) :=
  Subgroup.normalizer (spHeisSubgroup m K : Set (Gsp (spForm (m + 1) K)))

/-- The Heisenberg subgroup viewed as a normal subgroup of `spHeisNorm m K`. -/
noncomputable def spHeisQ (m : ℕ) (K : Type) [Field K] : Subgroup (spHeisNorm m K) :=
  (spHeisSubgroup m K).subgroupOf (spHeisNorm m K)

theorem spHeisQ_normal : (spHeisQ m K).Normal :=
  Subgroup.normal_in_normalizer

/-- Constructor for elements of `spHeisQ m K`. -/
noncomputable def mkSpHeisQ (w : Fin m ⊕ Fin m → K) (c : K) : spHeisQ m K :=
  ⟨⟨spHeis w c, Subgroup.le_normalizer ⟨w, c, rfl⟩⟩, w, c, rfl⟩

@[simp] theorem coe_mkSpHeisQ (w : Fin m ⊕ Fin m → K) (c : K) :
    ((mkSpHeisQ w c : spHeisQ m K) : Gsp (spForm (m + 1) K)) = spHeis w c := rfl

theorem mkSpHeisQ_eq_iff {w₁ w₂ : Fin m ⊕ Fin m → K} {c₁ c₂ : K} :
    mkSpHeisQ w₁ c₁ = mkSpHeisQ w₂ c₂ ↔ w₁ = w₂ ∧ c₁ = c₂ := by
  constructor
  · intro h
    exact spHeis_eq_iff.mp (congrArg (fun x : spHeisQ m K => (x.1 : Gsp (spForm (m + 1) K))) h)
  · rintro ⟨rfl, rfl⟩
    rfl

theorem mkSpHeisQ_injective :
    Function.Injective (fun p : (Fin m ⊕ Fin m → K) × K => mkSpHeisQ p.1 p.2) := by
  rintro ⟨w₁, c₁⟩ ⟨w₂, c₂⟩ h
  obtain ⟨rfl, rfl⟩ := mkSpHeisQ_eq_iff.mp h
  rfl

theorem mkSpHeisQ_surjective :
    Function.Surjective (fun p : (Fin m ⊕ Fin m → K) × K => mkSpHeisQ p.1 p.2) := by
  rintro ⟨⟨_, _⟩, w, c, hwc⟩
  exact ⟨(w, c), Subtype.ext (Subtype.ext hwc)⟩

/-- Bijection `(Fin m ⊕ Fin m → K) × K ≃ spHeisQ m K`. -/
noncomputable def spHeisQEquiv : (Fin m ⊕ Fin m → K) × K ≃ spHeisQ m K :=
  Equiv.ofBijective (fun p => mkSpHeisQ p.1 p.2) ⟨mkSpHeisQ_injective, mkSpHeisQ_surjective⟩

@[simp] theorem mkSpHeisQ_zero_zero : mkSpHeisQ (0 : Fin m ⊕ Fin m → K) (0 : K) = 1 :=
  Subtype.ext (Subtype.ext spHeis_zero_zero)

theorem mkSpHeisQ_mul (w₁ w₂ : Fin m ⊕ Fin m → K) (c₁ c₂ : K) :
    mkSpHeisQ w₁ c₁ * mkSpHeisQ w₂ c₂ = mkSpHeisQ (w₁ + w₂) (c₁ + c₂ + spForm m K w₂ w₁) :=
  Subtype.ext (Subtype.ext (spHeis_mul w₁ w₂ c₁ c₂))

theorem mkSpHeisQ_inv (w : Fin m ⊕ Fin m → K) (c : K) :
    (mkSpHeisQ w c)⁻¹ = mkSpHeisQ (-w) (-c) :=
  Subtype.ext (Subtype.ext (spHeis_inv w c))

theorem mkSpHeisQ_comm (w₁ w₂ : Fin m ⊕ Fin m → K) (c₁ c₂ : K) :
    ⁅mkSpHeisQ w₁ c₁, mkSpHeisQ w₂ c₂⁆ = mkSpHeisQ 0 (2 * spForm m K w₂ w₁) :=
  Subtype.ext (Subtype.ext (spHeis_comm w₁ w₂ c₁ c₂))

/-- The center `Z(Q) = { mkSpHeisQ 0 c | c : K }` of `spHeisQ m K`. -/
def spHeisZ (m : ℕ) (K : Type) [Field K] : Subgroup (spHeisQ m K) where
  carrier := { q | ∃ c : K, mkSpHeisQ 0 c = q }
  one_mem' := ⟨0, mkSpHeisQ_zero_zero⟩
  mul_mem' := by
    rintro _ _ ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
    refine ⟨c₁ + c₂, ?_⟩
    rw [mkSpHeisQ_mul, add_zero, spForm_self, add_zero]
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    refine ⟨-c, ?_⟩
    rw [mkSpHeisQ_inv, neg_zero]

/-- Bijection `K ≃ spHeisZ m K`. -/
noncomputable def spHeisZEquiv : K ≃ spHeisZ m K :=
  Equiv.ofBijective (fun c => ⟨mkSpHeisQ 0 c, c, rfl⟩)
    ⟨fun _ _ h => (mkSpHeisQ_eq_iff.mp (congrArg Subtype.val h)).2,
     fun ⟨_, c, hc⟩ => ⟨c, Subtype.ext hc⟩⟩

theorem mem_spHeisZ_iff (w : Fin m ⊕ Fin m → K) (c : K) :
    mkSpHeisQ w c ∈ spHeisZ m K ↔ w = 0 := by
  constructor
  · rintro ⟨c', hc'⟩
    exact (mkSpHeisQ_eq_iff.mp hc').1.symm
  · rintro rfl
    exact ⟨c, rfl⟩

theorem spHeisZ_le_center : spHeisZ m K ≤ Subgroup.center (spHeisQ m K) := by
  rintro _ ⟨c, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨⟨w, d⟩, rfl⟩ := mkSpHeisQ_surjective q
  change mkSpHeisQ w d * mkSpHeisQ 0 c = mkSpHeisQ 0 c * mkSpHeisQ w d
  rw [mkSpHeisQ_mul, mkSpHeisQ_mul, add_zero, zero_add, map_zero, LinearMap.zero_apply,
    map_zero (spForm m K w), add_zero, add_zero, add_comm d c]

theorem commutator_mem_spHeisZ (x y : spHeisQ m K) : ⁅x, y⁆ ∈ spHeisZ m K := by
  obtain ⟨⟨w₁, c₁⟩, rfl⟩ := mkSpHeisQ_surjective x
  obtain ⟨⟨w₂, c₂⟩, rfl⟩ := mkSpHeisQ_surjective y
  change ⁅mkSpHeisQ w₁ c₁, mkSpHeisQ w₂ c₂⁆ ∈ spHeisZ m K
  rw [mkSpHeisQ_comm]
  exact ⟨2 * spForm m K w₂ w₁, rfl⟩

theorem mkSpHeisQ_zero_pow (c : K) (k : ℕ) :
    (mkSpHeisQ (0 : Fin m ⊕ Fin m → K) c) ^ k = mkSpHeisQ 0 (k • c) := by
  induction k with
  | zero => simp [mkSpHeisQ_zero_zero]
  | succ k ih =>
    rw [pow_succ, ih, mkSpHeisQ_mul, add_zero, spForm_self, add_zero, succ_nsmul]

theorem pow_char_eq_one_of_mem_spHeisZ (p : ℕ) [CharP K p] {z : spHeisQ m K}
    (hz : z ∈ spHeisZ m K) : z ^ p = 1 := by
  obtain ⟨c, rfl⟩ := hz
  rw [mkSpHeisQ_zero_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, mkSpHeisQ_zero_zero]

theorem exists_mkSpHeisQ_pow (w : Fin m ⊕ Fin m → K) (c : K) (k : ℕ) :
    ∃ d : K, (mkSpHeisQ w c) ^ k = mkSpHeisQ (k • w) d := by
  induction k with
  | zero => exact ⟨0, by simp [mkSpHeisQ_zero_zero]⟩
  | succ k ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨d + c + spForm m K w (k • w), ?_⟩
    rw [pow_succ, hd, mkSpHeisQ_mul, succ_nsmul]

theorem pow_char_mem_spHeisZ (p : ℕ) [CharP K p] (x : spHeisQ m K) :
    x ^ p ∈ spHeisZ m K := by
  obtain ⟨⟨w, c⟩, rfl⟩ := mkSpHeisQ_surjective x
  obtain ⟨d, hd⟩ := exists_mkSpHeisQ_pow w c p
  have hpw : p • w = 0 := by
    rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
  change (mkSpHeisQ w c) ^ p ∈ spHeisZ m K
  rw [hd, hpw]
  exact ⟨d, rfl⟩

theorem exists_commutator_eq_of_not_mem_spHeisZ (h2 : (2 : K) ≠ 0) {x : spHeisQ m K}
    (hx : x ∉ spHeisZ m K) {z : spHeisQ m K} (hz : z ∈ spHeisZ m K) :
    ∃ y : spHeisQ m K, ⁅x, y⁆ = z := by
  obtain ⟨⟨w₁, c₁⟩, rfl⟩ := mkSpHeisQ_surjective x
  obtain ⟨t, rfl⟩ := hz
  have hw₁ : w₁ ≠ 0 := by rwa [mem_spHeisZ_iff] at hx
  obtain ⟨u, hu⟩ : ∃ u : Fin m ⊕ Fin m → K, spForm m K w₁ u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw₁ (spForm_nondegenerate.1 w₁ hcon)
  have huw₁ : spForm m K u w₁ ≠ 0 := by
    rw [spForm_swap]
    exact neg_ne_zero.mpr hu
  have h2u : 2 * spForm m K u w₁ ≠ 0 := mul_ne_zero h2 huw₁
  refine ⟨mkSpHeisQ ((t * (2 * spForm m K u w₁)⁻¹) • u) 0, ?_⟩
  change ⁅mkSpHeisQ w₁ c₁, mkSpHeisQ ((t * (2 * spForm m K u w₁)⁻¹) • u) 0⁆ = mkSpHeisQ 0 t
  rw [mkSpHeisQ_comm, map_smul, LinearMap.smul_apply, smul_eq_mul]
  congr 1
  calc 2 * (t * (2 * spForm m K u w₁)⁻¹ * spForm m K u w₁)
      = t * ((2 * spForm m K u w₁) * (2 * spForm m K u w₁)⁻¹) := by ring
    _ = t := by rw [mul_inv_cancel₀ h2u, mul_one]

/-- Every `extGsp g` normalizes `spHeisSubgroup m K`. -/
theorem extGsp_mem_spHeisNorm (g : Gsp (spForm m K)) :
    extGsp g ∈ spHeisNorm m K := by
  rw [spHeisNorm, Subgroup.mem_normalizer_iff]
  rintro _
  constructor
  · rintro ⟨w, c, rfl⟩
    exact ⟨g.app w, c, (extGsp_conj_spHeis g w c).symm⟩
  · intro h
    obtain ⟨w, c, hwc⟩ := h
    refine ⟨g⁻¹.app w, c, ?_⟩
    have h1 := congrArg (fun x => extGsp g⁻¹ * x * (extGsp g⁻¹)⁻¹) hwc.symm
    have hinv : extGsp g⁻¹ = (extGsp g)⁻¹ := by
      apply Subtype.ext
      apply Units.ext
      rfl
    rw [extGsp_conj_spHeis] at h1
    rw [← h1, hinv]
    group

/-- Element of `spHeisNorm m K` induced by `g : Gsp (spForm m K)`. -/
noncomputable def extSpHeisNorm (g : Gsp (spForm m K)) : spHeisNorm m K :=
  ⟨extGsp g, extGsp_mem_spHeisNorm g⟩

theorem conjQ_extSpHeisNorm (g : Gsp (spForm m K)) (w : Fin m ⊕ Fin m → K) (c : K) :
    conjQ spHeisQ_normal (extSpHeisNorm g) (mkSpHeisQ w c) = mkSpHeisQ (g.app w) c :=
  Subtype.ext (Subtype.ext (extGsp_conj_spHeis g w c))

/-- The normalizer `spHeisNorm m K` acts transitively on `spHeisQ m K \ spHeisZ m K` up to
`spHeisZ m K`. -/
theorem exists_conjQ_mul_eq_of_not_mem_spHeisZ {x : spHeisQ m K} (hx : x ∉ spHeisZ m K)
    {y : spHeisQ m K} (hy : y ∉ spHeisZ m K) :
    ∃ g : spHeisNorm m K, ∃ z ∈ spHeisZ m K, conjQ spHeisQ_normal g x * z = y := by
  obtain ⟨⟨w₁, c₁⟩, rfl⟩ := mkSpHeisQ_surjective x
  obtain ⟨⟨w₂, c₂⟩, rfl⟩ := mkSpHeisQ_surjective y
  have hw₁ : w₁ ≠ 0 := by rwa [mem_spHeisZ_iff] at hx
  have hw₂ : w₂ ≠ 0 := by rwa [mem_spHeisZ_iff] at hy
  obtain ⟨g, hg⟩ := exists_gsp_apply_eq spForm_isAlt spForm_nondegenerate hw₁ hw₂
  refine ⟨extSpHeisNorm g, mkSpHeisQ 0 (c₂ - c₁), ⟨c₂ - c₁, rfl⟩, ?_⟩
  change conjQ spHeisQ_normal (extSpHeisNorm g) (mkSpHeisQ w₁ c₁) * mkSpHeisQ 0 (c₂ - c₁) =
    mkSpHeisQ w₂ c₂
  rw [conjQ_extSpHeisNorm, hg, mkSpHeisQ_mul, add_zero, map_zero, LinearMap.zero_apply,
    add_zero, add_sub_cancel]

/-- The index of `spHeisZ m K` in `spHeisQ m K` is `Nat.card K ^ (2 * m)`. -/
theorem index_spHeisZ [Finite K] :
    (spHeisZ m K).index = Nat.card K ^ (2 * m) := by
  have : Finite (spHeisQ m K) := Finite.of_equiv _ spHeisQEquiv
  have hmul := Subgroup.index_mul_card (spHeisZ m K)
  have hV : Nat.card (Fin m ⊕ Fin m → K) = Nat.card K ^ (2 * m) := by
    rw [Nat.card_fun, Nat.card_sum, Nat.card_fin, ← two_mul]
  have hQ : Nat.card (spHeisQ m K) = Nat.card K ^ (2 * m) * Nat.card K := by
    rw [← Nat.card_congr spHeisQEquiv, Nat.card_prod, hV]
  have hZ : Nat.card (spHeisZ m K) = Nat.card K :=
    (Nat.card_congr spHeisZEquiv).symm
  rw [hQ, hZ] at hmul
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul

/-- Canonical homomorphism from `spHeisNorm m K` to `StatedProj (StatedSp (m + 1) K)`. -/
noncomputable def toStatedProjHom (m : ℕ) (K : Type) [Field K] :
    spHeisNorm m K →* StatedProj (StatedSp (m + 1) K) :=
  (QuotientGroup.mk'
      ((StatedScalars (Fin (m + 1) ⊕ Fin (m + 1)) K).subgroupOf (StatedSp (m + 1) K))).comp
    ((spEquiv (m := m + 1) (K := K)).symm.toMonoidHom.comp (spHeisNorm m K).subtype)

theorem map_spHeisZ_toStatedProjHom_ne_bot :
    ((spHeisZ m K).map (spHeisQ m K).subtype).map (toStatedProjHom m K) ≠ ⊥ := by
  rw [ne_eq, Subgroup.eq_bot_iff_forall]
  push Not
  let z₁ : spHeisQ m K := mkSpHeisQ 0 1
  have hz₁ : z₁ ∈ spHeisZ m K := ⟨1, rfl⟩
  refine ⟨toStatedProjHom m K z₁.1, ⟨z₁.1, ⟨z₁, hz₁, rfl⟩, rfl⟩, ?_⟩
  intro h1
  change QuotientGroup.mk' _ (spEquiv.symm (spHeis 0 1)) = 1 at h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    StatedScalars, MonoidHom.mem_range] at h1
  obtain ⟨u, hu⟩ := h1
  have happ : ∀ v : Fin (m + 1) ⊕ Fin (m + 1) → K, (spHeis 0 1).app v = (u : K) • v := by
    intro v
    have h2 := spEquiv_app (spEquiv.symm (spHeis 0 1)) v
    rw [MulEquiv.apply_symm_apply] at h2
    rw [h2, ← hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext k
    simp [Matrix.mulVec_diagonal]
  have he := congrFun (happ (spE0 m K)) (Sum.inl 0)
  rw [spHeis_app_spE0] at he
  simp only [Pi.smul_apply, spE0_inl_zero, smul_eq_mul, mul_one] at he
  have hf := congrFun (happ (spF0 m K)) (Sum.inl 0)
  rw [spHeis_app_spF0, ← he] at hf
  simp only [Pi.sub_apply, Pi.smul_apply, spF0_inl_zero, embSpVec_zero,
    spE0_inl_zero, sub_zero, one_smul, zero_sub, neg_eq_zero, one_ne_zero] at hf

end SymplecticHeisenberg

/-! ### Minimum subgroup index and `symplecticCase_odd` -/

open SymplecticHeisenberg

/-- Every proper subgroup `H` of `PSp(2n, p^f)` (`n ≥ 2`, `p ≠ 2`) has index at least
`p * (p ^ f) ^ (2 * n - 2)`, proved from the point-radical Heisenberg subgroup `spHeisQ` and
its normalizer action. -/
theorem index_ge_of_statedClassicalModel_psp_odd {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSp n p f) (hp2 : p ≠ 2) {H : Subgroup S} (hH : H ≠ ⊤) :
    p * (p ^ f) ^ (2 * n - 2) ≤ H.index := by
  have : IsSimpleGroup S := isSimpleGroup_of_statedClassicalModel_PSp S n p f h
  obtain ⟨⟨hp, hf, hn, _⟩, K, _, _, hK, ⟨eS⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := Maroti.charP_of_card_eq hp hf hK
  have h2 : (2 : K) ≠ 0 := Maroti.two_ne_zero_of_charP p hp2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : Finite S := Finite.of_equiv _ eS.symm.toEquiv
  have : Finite (Gsp (spForm (m + 1) K)) :=
    Finite.of_equiv _ (spEquiv (m := m + 1) (K := K)).toEquiv
  let fHom : spHeisNorm m K →* S :=
    eS.symm.toMonoidHom.comp (toStatedProjHom m K)
  have hZf : ((spHeisZ m K).map (spHeisQ m K).subtype).map fHom ≠ ⊥ := by
    change ((spHeisZ m K).map (spHeisQ m K).subtype).map
      (eS.symm.toMonoidHom.comp (toStatedProjHom m K)) ≠ ⊥
    rw [← Subgroup.map_map]
    intro hbot
    apply map_spHeisZ_toStatedProjHom_ne_bot (m := m) (K := K)
    apply Subgroup.map_injective (f := eS.symm.toMonoidHom) eS.symm.injective
    rw [hbot, Subgroup.map_bot]
  have hidx := mul_index_center_le_index_of_map_ne_bot_of_ne_top
    (p := p)
    spHeisZ_le_center
    commutator_mem_spHeisZ
    (fun _ hz => pow_char_eq_one_of_mem_spHeisZ p hz)
    (pow_char_mem_spHeisZ p)
    (fun _ hx _ hz => exists_commutator_eq_of_not_mem_spHeisZ h2 hx hz)
    spHeisQ_normal hH fHom hZf
    (fun _ hx _ hy => exists_conjQ_mul_eq_of_not_mem_spHeisZ hx hy)
  rw [index_spHeisZ, hK] at hidx
  rwa [show 2 * (m + 1) - 2 = 2 * m by omega]

/-- Theorem 1.1 for almost simple groups with socle `PSp(2n, p^f)` (`n ≥ 2`, `p` odd). -/
theorem symplecticCase_odd : AlmostSimpleCase SymplecticSocleOdd := by
  intro α _ G S _ _ hAS ⟨n, p, f, hp2, hModel⟩
  right; right
  have hp : p.Prime := hModel.1.1
  have hf : 1 ≤ f := hModel.1.2.1
  have hc0 : 0 < 2 * f * Nat.gcd 2 (p ^ f - 1) :=
    Nat.mul_pos (by omega) (Nat.gcd_pos_of_pos_left _ (by norm_num))
  exact hAS.card_le_bound_of_outerAut_dvd hc0
    (fun H hH => index_ge_of_statedClassicalModel_psp_odd hModel hp2 hH)
    (card_outerAut_psp_dvd hModel)
    (card_mul_outer_le_bound_psp_odd hModel hp2)

end Maroti
