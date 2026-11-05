module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
import Maroti.Sporadic.CubicWitness
import CFSG.Sporadic.McL
import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCubData
import CFSG.Certificates.Kernel.OpsLayKSound
import Certificates.Kernel.LocalComp.F3.McL
import all CFSG.Blueprint.NativeSporadic

/-!
# Sporadic Simple Group `McL`

This file proves Maróti's bound `Nat.card G ≤ bound (Nat.card α)` for primitive almost simple
groups `G` whose socle `S` is isomorphic to McLaughlin's group `McL`.

Using `CFSG.AGLEmbedding.SporCubic.mclSylow5HData` and `CFSG.KD.LC.F3.McL.sylow5H_K`, `McL` has
an extraspecial Sylow `5`-subgroup `Q` of order `5³ = 125` and exponent `5` normalized by an
element `h` acting on `Q / Z(Q) ≅ (ZMod 5)²` by the matrix `[[1, 4], [3, 3]]` with irreducible
characteristic polynomial `λ² + λ + 1`. By `Maroti.CubicWitness.two_mul_sq_le_index_of_ne_top`,
every proper subgroup of `McL` has index at least `2 * 5² = 50 ≥ 45`.
-/

@[expose] public section

namespace Maroti

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.SporCubic
  CFSG.KD.LC.F3

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem mcl_cubicCheck : (ops3 21).cubicCheck mclSylow5HData = true :=
  CFSG.KC.OpsLayK.cubK_sound McL.lay_ok rfl rfl McL.decA McL.decB
    ((rfl : mclSylow5HData.seedA = NativeSporadic.McLSeed1).trans McL.LA_eq)
    ((rfl : mclSylow5HData.seedB = NativeSporadic.McLSeed2).trans McL.LB_eq)
    McL.sylow5H_K

private theorem mcl_hirr : ∀ (i j : ZMod 5), (i ≠ 0 ∨ j ≠ 0) →
    ∀ (m : ZMod 5),
      (mclSylow5HData.a : ZMod 5) * i + (mclSylow5HData.c : ZMod 5) * j ≠ m * i ∨
      (mclSylow5HData.b : ZMod 5) * i + (mclSylow5HData.d : ZMod 5) * j ≠ m * j := by
  decide

/-- Every proper subgroup of `McL` has index at least `50`. -/
theorem index_ge_McL {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .McL) {H : Subgroup S} (hH : H ≠ ⊤) :
    50 ≤ H.index := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, y, h, hx, hy, hz1, hzx, hzy, hcard, hhx, hhy, hhz⟩ :=
    (spec3 21).cubic_of_check mclSylow5HData mcl_cubicCheck
  exact CubicWitness.two_mul_sq_le_index_of_ne_top (r := 5) hx hy hz1 hzx hzy hcard hhx hhy hhz
    mcl_hirr e hH

/-- Maróti's bound for primitive almost simple groups with socle `McL`. -/
theorem sporadicCase_McL {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type)
    [Group S] [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .McL)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 898128000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.McL.card_McL
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 50) (c := 2) (by decide)
    (fun H hH => index_ge_McL e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.McL, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

end Maroti
