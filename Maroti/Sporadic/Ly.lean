module

public import Maroti.Sporadic.AutBound
public import Maroti.Sporadic.ExtraspecialCoord
import CFSG.RankThree.Native.LyFiveSpec
import CFSG.Sporadic.Ly

/-!
# Lyons Group `Ly`

This file proves Maróti's bound for the Lyons sporadic simple group `Ly`.
Using the extraspecial `5`-subgroup `fiveQ lyFiveXJ lyFiveVJ ≤ CFSG.Sporadic.Ly.J` of order
`5 ^ 5 = 3125` and exponent `5`, together with the normalizing elements `lyFiveAJ, lyFiveBJ` acting
irreducibly on `Q ⧸ Z(Q) ≅ (ZMod 5)⁴` via `lyFiveAbar` and `lyFiveBbar`
(`CFSG.RankThree.Native.lyFiveMRelJ`), every proper subgroup `H` of `Ly` has index at least
`2 * 5 ^ 3 = 250 ≥ 169 = n₀(2|Ly|)`.
-/

@[expose] public section

namespace Maroti

open Subgroup CFSG.Blueprint CFSG.RankThree.Native Maroti.ExtraspecialCoord
open scoped Matrix

private theorem ly_hirr : IrreduciblePair lyFiveAbar lyFiveBbar := by
  decide +kernel

/-- Every proper subgroup of `Ly` has index at least `250`. -/
theorem index_ge_Ly {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .Ly) {H : Subgroup S} (hH : H ≠ ⊤) :
    250 ≤ H.index := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let hM := lyFiveMRelJ
  let hQ := hM.q
  let e' : S ≃* CFSG.Sporadic.Ly.J := e.trans CFSG.Sporadic.Ly.lyEquivJ
  have : Finite CFSG.Sporadic.Ly.J := Finite.of_equiv S e'.toEquiv
  set Q : Subgroup CFSG.Sporadic.Ly.J := fiveQ lyFiveXJ lyFiveVJ
  have hcard : Nat.card Q = 5 ^ 5 := hQ.card_fiveQ
  have hcenter : Nat.card (center Q) = 5 := hQ.card_center
  have hcomm : commutator Q ≤ center Q := hQ.commutator_eq_center.le
  have hexp : ∀ q : Q, q ^ 5 = 1 := fun q => Subtype.ext (hQ.pow_five_of_mem q.2)
  have hψ_ker : ∀ q : Q, hQ.coord q = 0 ↔ q ∈ center Q :=
    fun q => (hQ.coord_eq_zero_iff q).trans (hQ.mem_center_iff q).symm
  have hg₁ : ∀ q ∈ Q, lyFiveAJ * q * lyFiveAJ⁻¹ ∈ Q := fun _ hq => hM.a_conj_mem hq
  have hg₂ : ∀ q ∈ Q, lyFiveBJ * q * lyFiveBJ⁻¹ ∈ Q := fun _ hq => hM.b_conj_mem hq
  have hA₁ : ∀ q : Q,
      hQ.coord ⟨lyFiveAJ * (q : CFSG.Sporadic.Ly.J) * lyFiveAJ⁻¹, hg₁ q.1 q.2⟩ =
        lyFiveAbar *ᵥ hQ.coord q := by
    intro q
    change hQ.coord (hM.conjQ ⟨lyFiveAJ, FiveMRel.a_mem⟩ q) = lyFiveAbar *ᵥ hQ.coord q
    rw [hM.coord_conjQ, hM.rhoMat_a]
  have hA₂ : ∀ q : Q,
      hQ.coord ⟨lyFiveBJ * (q : CFSG.Sporadic.Ly.J) * lyFiveBJ⁻¹, hg₂ q.1 q.2⟩ =
        lyFiveBbar *ᵥ hQ.coord q := by
    intro q
    change hQ.coord (hM.conjQ ⟨lyFiveBJ, FiveMRel.b_mem⟩ q) = lyFiveBbar *ᵥ hQ.coord q
    rw [hM.coord_conjQ, hM.rhoMat_b]
  exact two_mul_cube_le_index_of_ne_top (by decide : 3 ≤ 5) hcard hcenter hcomm hexp
    hQ.coord hM.coord_one hQ.coord_mul hψ_ker hg₁ hg₂ hA₁ hA₂ ly_hirr e' hH

/-- Maróti's bound for primitive almost simple groups with socle `Ly`. -/
theorem sporadicCase_Ly {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type)
    [Group S] [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .Ly)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 51765179004000000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Ly.card_Ly
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 250) (c := 2) (by decide)
    (fun H hH => index_ge_Ly e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.Ly, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

end Maroti
