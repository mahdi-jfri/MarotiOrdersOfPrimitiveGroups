module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
import Maroti.Sporadic.CubicWitness
import CFSG.RankThree.PartOne.MultRes.Co3
import all CFSG.Blueprint.NativeSporadic

/-!
# Sporadic Simple Group `Co₃`

This file proves Maróti's bound `Nat.card G ≤ bound (Nat.card α)` for primitive almost simple
groups `G` whose socle `S` is isomorphic to Conway's third group `Co₃`.

Using `CFSG.RankThree.PartOne.MultRes.Co3_sylow5_cubic_witness`, `Co₃` has an extraspecial
Sylow `5`-subgroup `Q` of order `5³ = 125` and exponent `5` normalized by an element `h` acting on
`Q / Z(Q) ≅ (ZMod 5)²` by the matrix `[[1, 2], [2, 2]]`, whose first and second powers have no
eigenvalue over `ZMod 5`. By `Maroti.CubicWitness.three_mul_sq_le_index_of_ne_top`, every proper
subgroup of `Co₃` has index at least `3 * 5² = 75 > 64`.
-/

@[expose] public section

namespace Maroti

open CFSG.Blueprint CFSG.RankThree.PartOne.MultRes

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem co3_hirr₃ : ∀ i j : ZMod 5, (i ≠ 0 ∨ j ≠ 0) →
    (∀ m : ZMod 5, (1 * i + 2 * j : ZMod 5) ≠ m * i ∨ (2 * i + 2 * j : ZMod 5) ≠ m * j) ∧
    (∀ m : ZMod 5,
      (1 * (1 * i + 2 * j) + 2 * (2 * i + 2 * j) : ZMod 5) ≠ m * i ∨
      (2 * (1 * i + 2 * j) + 2 * (2 * i + 2 * j) : ZMod 5) ≠ m * j) := by
  decide

/-- Every proper subgroup of `Co₃` has index at least `75`. -/
theorem index_ge_Co3 {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .Co3) {H : Subgroup S} (hH : H ≠ ⊤) :
    75 ≤ H.index := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, y, h, hx, hy, hz1, hzx, hzy, hcard, hhx, hhy, hhz⟩ := Co3_sylow5_cubic_witness
  exact CubicWitness.three_mul_sq_le_index_of_ne_top (r := 5) (by decide)
    hx hy hz1 hzx hzy hcard hhx hhy hhz co3_hirr₃ e hH

/-- Maróti's bound for primitive almost simple groups with socle `Co₃`. -/
theorem sporadicCase_Co3 {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type)
    [Group S] [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .Co3)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 495766656000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Schreier.Co3.card_Co3_of_perm
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 75) (c := 2) (by decide)
    (fun H hH => index_ge_Co3 e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.Co3, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

end Maroti
