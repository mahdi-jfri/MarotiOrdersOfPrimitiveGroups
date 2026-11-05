module

public import Maroti.Sporadic.AutBound
public import Maroti.Sporadic.ExtraspecialCoord
import CFSG.RankThree.PartOne.KS.HNFiveCheck
import CFSG.Sporadic.HN

/-!
# Harada–Norton Group `HN`

This file proves Maróti's bound for the Harada–Norton sporadic simple group `HN`.
Using the extraspecial `5`-subgroup `QG qJ ≤ CFSG.Sporadic.GLQ.HNTwoRank.J` of order
`5 ^ 5 = 3125` and exponent `5`, together with the normalizing elements `xJ⁻¹` and `(rJ 0)⁻¹`
acting irreducibly on `Q ⧸ Z(Q) ≅ (ZMod 5)⁴` via `Xmᵀ` and `(Bm 0)ᵀ`
(`CFSG.RankThree.PartOne.KS.HNFive.hnFive_rel`), every proper subgroup `H` of `HN` has index at
least `2 * 5 ^ 3 = 250 ≥ 135 = n₀(2|HN|)`.
-/

@[expose] public section

namespace Maroti

open Subgroup CFSG.Blueprint CFSG.Monster.B.Pinned CFSG.RankThree.PartOne.KS.HNFive
  CFSG.Sporadic.GLQ CFSG.Sporadic.GLQ.HNTwoRank Maroti.ExtraspecialCoord
open scoped Matrix

attribute [local irreducible] Rg

private theorem hn_hirr : IrreduciblePair Xmᵀ (Bm 0)ᵀ := by
  decide +kernel

/-- Every proper subgroup of `HN` has index at least `250`. -/
theorem index_ge_HN {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .HN) {H : Subgroup S} (hH : H ≠ ⊤) :
    250 ≤ H.index := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let e' : S ≃* J := e.trans hnEquivJ
  have : Finite J := Finite.of_equiv S e'.toEquiv
  let qJ : Fin 4 → J := fun j => ⟨Rg (iQ j), Rg_mem (iQ j)⟩
  let zJ : J := ⟨Rg iZ, Rg_mem iZ⟩
  let xJ : J := ⟨Rg iX, Rg_mem iX⟩
  let rJ : Fin 3 → J := fun j => ⟨Rg (iR j), Rg_mem (iR j)⟩
  have hrel : Rel qJ zJ xJ rJ Mm XU cx BU cr :=
    Rel.of_injective J.subtype Subtype.val_injective (q := qJ) (z := zJ) (x := xJ) (r := rJ)
      hnFive_rel
  set Q : Subgroup J := QG qJ
  have hcard : Nat.card Q = 5 ^ 5 := hrel.card_Q
  have hcenter : Nat.card (center Q) = 5 := hrel.card_center_Q
  have hcomm : commutator Q ≤ center Q := hrel.center_Q_eq_commutator.symm.le
  have hexp : ∀ q : Q, q ^ 5 = 1 := fun q => Subtype.ext (hrel.pow_five_of_mem q.2)
  let ψ : Q → (Fin 4 → ZMod 5) := fun q => coord 5 qJ zJ Mm (q : J)
  have hψ_one : ψ 1 = 0 := hrel.commData.coord_one
  have hψ_mul : ∀ a b : Q, ψ (a * b) = ψ a + ψ b :=
    fun a b => hrel.commData.coord_mul a.2 b.2
  have hψ_ker : ∀ q : Q, ψ q = 0 ↔ q ∈ center Q := by
    intro q
    rw [hrel.commData.center_eq, ← hrel.commData.ker_coordHom, MonoidHom.mem_ker,
      CommData.coordHom_apply]
    exact (Multiplicative.ofAdd.injective.eq_iff' rfl).symm
  have hg₁ : ∀ q ∈ Q, xJ⁻¹ * q * (xJ⁻¹)⁻¹ ∈ Q := fun q hq => by
    rw [inv_inv]
    exact hrel.x_conj_Q q hq
  have hg₂ : ∀ q ∈ Q, (rJ 0)⁻¹ * q * ((rJ 0)⁻¹)⁻¹ ∈ Q := fun q hq => by
    rw [inv_inv]
    exact hrel.r_conj_Q 0 q hq
  have hA₁ : ∀ q : Q, ψ ⟨xJ⁻¹ * (q : J) * (xJ⁻¹)⁻¹, hg₁ q.1 q.2⟩ = Xmᵀ *ᵥ ψ q := by
    intro q
    change coord 5 qJ zJ Mm (xJ⁻¹ * (q : J) * (xJ⁻¹)⁻¹) = Xmᵀ *ᵥ coord 5 qJ zJ Mm (q : J)
    rw [inv_inv, hrel.commData.coord_conj hrel.conj_x_mem q.2, hrel.actMat_x, XU_val,
      Matrix.mulVec_transpose]
  have hA₂ : ∀ q : Q,
      ψ ⟨(rJ 0)⁻¹ * (q : J) * ((rJ 0)⁻¹)⁻¹, hg₂ q.1 q.2⟩ = (Bm 0)ᵀ *ᵥ ψ q := by
    intro q
    change coord 5 qJ zJ Mm ((rJ 0)⁻¹ * (q : J) * ((rJ 0)⁻¹)⁻¹) =
      (Bm 0)ᵀ *ᵥ coord 5 qJ zJ Mm (q : J)
    rw [inv_inv, hrel.commData.coord_conj (hrel.conj_r_mem 0) q.2, hrel.actMat_r 0, BU_val,
      Matrix.mulVec_transpose]
  exact two_mul_cube_le_index_of_ne_top (by decide : 3 ≤ 5) hcard hcenter hcomm hexp
    ψ hψ_one hψ_mul hψ_ker hg₁ hg₂ hA₁ hA₂ hn_hirr e' hH

/-- Maróti's bound for primitive almost simple groups with socle `HN`. -/
theorem sporadicCase_HN {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type)
    [Group S] [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .HN)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 273030912000000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.HN.card_HN
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 250) (c := 2) (by decide)
    (fun H hH => index_ge_HN e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.HN, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

end Maroti
