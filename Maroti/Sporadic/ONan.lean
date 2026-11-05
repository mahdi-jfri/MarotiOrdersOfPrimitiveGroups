module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
import Maroti.Sporadic.CubicWitness
import CFSG.Sporadic.ON
import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
import Certificates.Data.CFSGNative.MultRes.Witnesses
import CFSG.Certificates.Kernel.OpsLayKSound
import Certificates.Kernel.LocalComp.F3.ON
import all CFSG.Blueprint.NativeSporadic

/-!
# Sporadic Simple Group `O'N`

This file proves Maróti's bound `Nat.card G ≤ bound (Nat.card α)` for primitive almost simple
groups `G` whose socle `S` is isomorphic to O'Nan's group `O'N`.

Using `CFSG.SectionRank.Native.onMultData` and `CFSG.KD.LC.F3.ON.mult_K`, `O'N` has an
extraspecial Sylow `7`-subgroup `Q` of order `7³ = 343` and exponent `7` normalized by an
element `h` acting on `Q / Z(Q) ≅ (ZMod 7)²` by the matrix `[[0, 1], [6, 0]]` with irreducible
characteristic polynomial `λ² + 1`. By `Maroti.CubicWitness.two_mul_sq_le_index_of_ne_top`,
every proper subgroup of `O'N` has index at least `2 * 7² = 98 ≥ 64`.
-/

@[expose] public section

namespace Maroti

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.KD.LC.F3

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem on_cubicCheck : (ops3 154).cubicCheck onMultData = true :=
  CFSG.KC.OpsLayK.cubK_sound ON.lay_ok rfl rfl ON.decA ON.decB
    ((rfl : onMultData.seedA = NativeSporadic.ONSeed1).trans ON.LA_eq)
    ((rfl : onMultData.seedB = NativeSporadic.ONSeed2).trans ON.LB_eq)
    ON.mult_K

private theorem on_hirr : ∀ (i j : ZMod 7), (i ≠ 0 ∨ j ≠ 0) →
    ∀ (m : ZMod 7),
      (onMultData.a : ZMod 7) * i + (onMultData.c : ZMod 7) * j ≠ m * i ∨
      (onMultData.b : ZMod 7) * i + (onMultData.d : ZMod 7) * j ≠ m * j := by
  decide

/-- Every proper subgroup of `O'N` has index at least `98`. -/
theorem index_ge_ONan {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .ONan) {H : Subgroup S} (hH : H ≠ ⊤) :
    98 ≤ H.index := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨x, y, h, hx, hy, hz1, hzx, hzy, hcard, hhx, hhy, hhz⟩ :=
    (spec3 154).cubic_of_check onMultData on_cubicCheck
  exact CubicWitness.two_mul_sq_le_index_of_ne_top (r := 7) hx hy hz1 hzx hzy hcard hhx hhy hhz
    on_hirr e hH

/-- Maróti's bound for primitive almost simple groups with socle `O'N`. -/
theorem sporadicCase_ONan {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type)
    [Group S] [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .ONan)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 460815505920 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.ON.card_ON
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 98) (c := 2) (by decide)
    (fun H hH => index_ge_ONan e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.ONan, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

end Maroti
