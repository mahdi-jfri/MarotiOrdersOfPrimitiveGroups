module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
import Maroti.Sporadic.CubicWitness
import CFSG.Sporadic.J2
import CFSG.LocalAnalysis.SectionRank.Sporadic.J2Local

/-!
# Sporadic Simple Group `J₂`

This file proves Maróti's bound `Nat.card G ≤ bound (Nat.card α)` for primitive almost simple
groups `G` whose socle `S` is isomorphic to Janko's second group `J₂` (the Hall–Janko group).

Using `CFSG.SectionRank.J2_sylow3_cubic_witness`, `J₂` has an extraspecial Sylow `3`-subgroup
`Q` of order `27` and exponent `3` normalized by an element `h` acting on `Q / Z(Q) ≅ (ZMod 3)²`
with irreducible characteristic polynomial `λ² + λ + 2` (so neither `h` nor `h²` has an invariant
line). By `Maroti.CubicWitness.twentySeven_le_index_of_ne_top`, every proper subgroup of `J₂` has
index at least `27 ≥ 20`.
-/

@[expose] public section

namespace Maroti

open CFSG.Blueprint

/-- Every proper subgroup of `J₂` has index at least `27`. -/
theorem index_ge_J2 {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .J2) {H : Subgroup S} (hH : H ≠ ⊤) :
    27 ≤ H.index := by
  obtain ⟨x, y, h, hx, hy, hz1, hzx, hzy, hcard, hhx, hhy, hhz⟩ :=
    CFSG.SectionRank.J2_sylow3_cubic_witness
  exact CubicWitness.twentySeven_le_index_of_ne_top hx hy hz1 hzx hzy hcard hhx hhy hhz
    (by decide) e hH

/-- Maróti's bound for primitive almost simple groups with socle `J₂`. -/
theorem sporadicCase_J2 {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type)
    [Group S] [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .J2)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 604800 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 27) (c := 2) (by decide)
    (fun H hH => index_ge_J2 e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.J2, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

end Maroti
