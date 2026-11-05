module

public import Maroti.Interface
import Maroti.Sporadic.CubicWitness
import CFSG.Open.StatedAPI
import CFSG.ClassicalGroups.Symplectic.Simple

/-!
# Minimum Degree of `PSp(6, 2)`

This file proves `Maroti.index_ge_pSp_six_two`: every proper subgroup `H ≠ ⊤` of a group `S`
satisfying `CFSG.Open.StatedClassicalModel S .PSp 3 2 1` (`PSp(6, 2) ≅ Sp(6, 2)`) has index at
least `23`, and in fact at least `27` (Maróti, Section 2, Step 2, page 634).

We exhibit explicit `6 × 6` symplectic matrices `xSp`, `ySp`, `hSp` in `StatedSp 3 (ZMod 2)` where
`xSp` and `ySp` generate an extraspecial `3^(1+2)_+` subgroup `Q` of order `27` and exponent `3`
coming from `SU(3, 2) ≤ Sp(6, 2)` (verified using
`CFSG.SectionRank.LocalWitness.mem_closure_normalForm` from
`CFSG/LocalAnalysis/SectionRank/Sporadic/LocalWitness.lean`), and `hSp` normalizes `Q` and acts on
`Q / Z(Q) ≅ (ZMod 3)²` as an element of order `8` (`[[2, 1], [2, 2]]`), so neither `hSp` nor `hSp²`
has an invariant line. Combining `Maroti.CubicWitness.twentySeven_le_index_of_not_mem` with
simplicity of `PSp(6, 2)`
(`CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp` in
`CFSG/ClassicalGroups/Symplectic/Simple.lean`) gives `27 ≤ H.index`.
-/

@[expose] public section

namespace Maroti

open Matrix Subgroup CFSG.Open CFSG.Open.StatedAPI
open scoped commutatorElement

namespace SymplecticSmall

/-- Decidable equality on `StatedSp 3 (ZMod 2)` induced by underlying `6 × 6` matrices. -/
instance : DecidableEq (StatedSp 3 (ZMod 2)) :=
  fun a b => decidable_of_iff
    (((a : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) =
     ((b : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)))
    ⟨fun h => Subtype.ext (Units.ext h),
     fun h => congrArg (fun g : StatedSp 3 (ZMod 2) =>
       ((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))) h⟩

/-- Helper constructor for elements of `StatedSp 3 (ZMod 2)` from explicit `6 × 6` matrices. -/
def mkSp62 (M Minv : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))
    (h1 : M * Minv = 1) (h2 : Minv * M = 1)
    (hJ : Mᵀ * fromBlocks 0 1 (-1) 0 * M = fromBlocks 0 1 (-1) 0) :
    StatedSp 3 (ZMod 2) :=
  ⟨⟨M, Minv, h1, h2⟩, mem_statedSp_iff.mpr hJ⟩

/-- First generator `x` of the extraspecial `3^(1+2)_+` subgroup in `StatedSp 3 (ZMod 2)`. -/
def xMat : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  fromBlocks
    !![0, 0, 0; 0, 1, 0; 1, 0, 0] !![0, 0, 1; 1, 1, 0; 0, 1, 1]
    !![0, 1, 1; 1, 1, 0; 0, 1, 0] !![0, 1, 1; 1, 1, 0; 0, 1, 0]

/-- Inverse of `xMat`. -/
def xInvMat : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  fromBlocks
    !![0, 1, 0; 1, 1, 1; 1, 0, 0] !![0, 1, 0; 0, 1, 1; 1, 0, 1]
    !![0, 1, 0; 1, 1, 1; 1, 0, 0] !![0, 0, 1; 0, 1, 0; 0, 0, 0]

/-- Second generator `y` of the extraspecial `3^(1+2)_+` subgroup in `StatedSp 3 (ZMod 2)`. -/
def yMat : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  fromBlocks
    !![0, 0, 0; 1, 0, 0; 0, 1, 0] !![0, 0, 1; 1, 1, 1; 1, 0, 1]
    !![0, 1, 1; 1, 0, 0; 0, 0, 0] !![0, 1, 1; 0, 1, 1; 0, 1, 1]

/-- Inverse of `yMat`. -/
def yInvMat : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  fromBlocks
    !![0, 0, 0; 1, 1, 1; 1, 1, 1] !![0, 1, 1; 0, 1, 0; 1, 1, 1]
    !![0, 1, 0; 1, 0, 0; 1, 0, 0] !![0, 1, 0; 0, 0, 1; 0, 0, 0]

/-- Normalizing element `h` of order `8` in `StatedSp 3 (ZMod 2)`. -/
def hMat : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  fromBlocks
    !![1, 0, 1; 1, 0, 0; 0, 1, 0] !![1, 1, 1; 0, 1, 1; 1, 1, 0]
    !![0, 0, 1; 0, 1, 1; 1, 1, 0] !![1, 0, 1; 1, 1, 1; 1, 1, 1]

/-- Inverse of `hMat`. -/
def hInvMat : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  fromBlocks
    !![1, 1, 1; 0, 1, 1; 1, 1, 1] !![1, 0, 1; 1, 1, 1; 1, 1, 0]
    !![0, 0, 1; 0, 1, 1; 1, 1, 0] !![1, 1, 0; 0, 0, 1; 1, 0, 0]

/-- First generator `xSp` in `StatedSp 3 (ZMod 2)`. -/
def xSp : StatedSp 3 (ZMod 2) :=
  mkSp62 xMat xInvMat (by decide) (by decide) (by decide)

/-- Second generator `ySp` in `StatedSp 3 (ZMod 2)`. -/
def ySp : StatedSp 3 (ZMod 2) :=
  mkSp62 yMat yInvMat (by decide) (by decide) (by decide)

/-- Normalizer element `hSp` in `StatedSp 3 (ZMod 2)`. -/
def hSp : StatedSp 3 (ZMod 2) :=
  mkSp62 hMat hInvMat (by decide) (by decide) (by decide)

private theorem xSp_pow_three : xSp ^ 3 = 1 := by decide

private theorem ySp_pow_three : ySp ^ 3 = 1 := by decide

private theorem comm_xSp_ySp_ne_one : ⁅xSp, ySp⁆ ≠ 1 := by
  rw [commutatorElement_def]
  decide

private theorem commute_comm_xSp : Commute ⁅xSp, ySp⁆ xSp := by
  rw [Commute, SemiconjBy, commutatorElement_def]
  decide

private theorem commute_comm_ySp : Commute ⁅xSp, ySp⁆ ySp := by
  rw [Commute, SemiconjBy, commutatorElement_def]
  decide

private theorem conj_hSp_xSp : hSp * xSp * hSp⁻¹ = xSp ^ 2 * ySp ^ 2 * ⁅xSp, ySp⁆ ^ 0 := by
  rw [commutatorElement_def]
  decide

private theorem conj_hSp_ySp : hSp * ySp * hSp⁻¹ = xSp ^ 1 * ySp ^ 2 * ⁅xSp, ySp⁆ ^ 0 := by
  rw [commutatorElement_def]
  decide

private theorem conj_hSp_comm : hSp * ⁅xSp, ySp⁆ * hSp⁻¹ = ⁅xSp, ySp⁆ ^ 2 := by
  rw [commutatorElement_def]
  decide

/-- Normal-form map `Fin 3 × Fin 3 × Fin 3 → StatedSp 3 (ZMod 2)`. -/
def nfMap (t : Fin 3 × Fin 3 × Fin 3) : StatedSp 3 (ZMod 2) :=
  xSp ^ (t.1 : ℕ) * ySp ^ (t.2.1 : ℕ) * (xSp * ySp * xSp⁻¹ * ySp⁻¹) ^ (t.2.2 : ℕ)

private theorem nfMap_injective : Function.Injective nfMap := by decide

private theorem card_closure_xSp_ySp :
    Nat.card (Subgroup.closure ({xSp, ySp} : Set (StatedSp 3 (ZMod 2)))) = 3 ^ 3 := by
  set Q := Subgroup.closure ({xSp, ySp} : Set (StatedSp 3 (ZMod 2)))
  have hxQ : xSp ∈ Q := Subgroup.subset_closure (by simp)
  have hyQ : ySp ∈ Q := Subgroup.subset_closure (by simp)
  have hzQ : ⁅xSp, ySp⁆ ∈ Q := CubicWitness.commutator_mem_closure_pair xSp ySp
  let F : Fin 3 × Fin 3 × Fin 3 → Q := fun t =>
    ⟨xSp ^ (t.1 : ℕ) * ySp ^ (t.2.1 : ℕ) * ⁅xSp, ySp⁆ ^ (t.2.2 : ℕ),
      Q.mul_mem (Q.mul_mem (Q.pow_mem hxQ _) (Q.pow_mem hyQ _)) (Q.pow_mem hzQ _)⟩
  have hF_inj : Function.Injective F := by
    intro a b hab
    apply nfMap_injective
    have hval := congrArg Subtype.val hab
    simpa [F, nfMap, commutatorElement_def] using hval
  have hF_surj : Function.Surjective F := fun g => by
    obtain ⟨i, j, k, hi, hj, hk, hg⟩ :=
      CFSG.SectionRank.LocalWitness.mem_closure_normalForm (by decide : 0 < 3)
        xSp_pow_three ySp_pow_three commute_comm_xSp commute_comm_ySp g.2
    exact ⟨(⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩), Subtype.ext hg.symm⟩
  have hcard : Nat.card (Fin 3 × Fin 3 × Fin 3) = Nat.card Q :=
    Nat.card_congr (Equiv.ofBijective F ⟨hF_inj, hF_surj⟩)
  rw [← hcard, Nat.card_prod, Nat.card_prod, Nat.card_fin]
  decide

/-- Every proper subgroup of a group `S` satisfying `StatedClassicalModel S .PSp 3 2 1` has index
at least `27`. -/
theorem twentySeven_le_index_pSp_six_two (S : Type) [Group S]
    (hS : StatedClassicalModel S .PSp 3 2 1) (H : Subgroup S) (hH : H ≠ ⊤) :
    27 ≤ H.index := by
  have : IsSimpleGroup S :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp S 3 2 1 hS
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨eS⟩⟩ := hS
  have : Finite S := Finite.of_equiv _ eS.symm.toEquiv
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  let _ : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK])
  let φ : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  let mapSp : StatedSp 3 (ZMod 2) →* StatedSp 3 K :=
    { toFun := fun g => ⟨Matrix.GeneralLinearGroup.map φ g.1, map_mem_statedSp φ g.2⟩
      map_one' := Subtype.ext (map_one (Matrix.GeneralLinearGroup.map φ))
      map_mul' := fun a b => Subtype.ext (map_mul (Matrix.GeneralLinearGroup.map φ) a.1 b.1) }
  have hmapSp_inj : Function.Injective mapSp := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    ext i j
    have hmat : ((mapSp a : StatedSp 3 K).1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
        ((mapSp b : StatedSp 3 K).1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) :=
      congrArg (fun g : StatedSp 3 K =>
        ((g : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)) hab
    exact φ.injective (congrFun (congrFun hmat i) j)
  let N : Subgroup (StatedSp 3 K) :=
    (StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K)
  have hN_bot : N = ⊥ := statedScalars_subgroupOf_statedSp_eq_bot
  have hmk_inj : Function.Injective (QuotientGroup.mk' N) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hN_bot]
  let f : StatedSp 3 (ZMod 2) →* S :=
    eS.symm.toMonoidHom.comp ((QuotientGroup.mk' N).comp mapSp)
  have hf_inj : Function.Injective f :=
    eS.symm.injective.comp (hmk_inj.comp hmapSp_inj)
  have hZne : Subgroup.zpowers ⁅xSp, ySp⁆ ≠ ⊥ :=
    Subgroup.zpowers_ne_bot.mpr comm_xSp_ySp_ne_one
  exact le_index_of_injective_of_forall_not_le_index hH f hf_inj hZne fun K₀ hZK₀ =>
    CubicWitness.twentySeven_le_index_of_not_mem
      xSp_pow_three ySp_pow_three comm_xSp_ySp_ne_one
      commute_comm_xSp commute_comm_ySp card_closure_xSp_ySp
      conj_hSp_xSp conj_hSp_ySp conj_hSp_comm
      (by decide)
      (fun hzK₀ => hZK₀ (Subgroup.zpowers_le.mpr hzK₀))

end SymplecticSmall

/-- Every proper subgroup `H ≠ ⊤` of `PSp(6, 2)` has index at least `23` (in fact at least `27`,
via `SU(3, 2) = 3^(1+2)_+ : Q₈ ≤ Sp(6, 2)`). -/
theorem index_ge_pSp_six_two (S : Type) [Group S]
    (hS : CFSG.Open.StatedClassicalModel S .PSp 3 2 1) (H : Subgroup S) (hH : H ≠ ⊤) :
    23 ≤ H.index :=
  (by decide : 23 ≤ 27).trans (SymplecticSmall.twentySeven_le_index_pSp_six_two S hS H hH)

end Maroti
