module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
public import Maroti.MinDegree.RootHeisenberg
public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.HeisCoord
import Certificates.Certificate129030
import CFSG.Sporadic.Fi23.Simple
import CFSG.Sporadic.FischerOddCore.Fi23Aut

/-!
# Sporadic Simple Group `Fi₂₃`

This file proves Maróti's bound `Nat.card G ≤ bound (Nat.card α)` for primitive almost simple
groups `G` whose socle `S` is isomorphic to Fischer's group `Fi₂₃` (Maróti, *On the orders of
primitive groups*, J. Algebra 258 (2002), Theorem 1.1).

The minimum degree lower bound `243 ≤ H.index` (hence `230 ≤ H.index`) uses the extraspecial
Heisenberg `3`-configuration `HeisCfg 3 4` of order `3 ^ 9` in `Fi₂₃` from
`Certificates.certificate129030` together with `RootHeisenbergData.mul_pow_le_index_of_ne_top`.
-/

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Maroti

open CFSG.Blueprint CFSG.Sporadic.Fi23 CFSG.Sporadic.FischerOddCore
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open CFSG.HardMathSupport.Solomon.Coordinator.B3B
open scoped commutatorElement

theorem comm_pow_of_comm {G : Type*} [Group G] {u v : G} (h : u * v = v * u)
    (a b : ℕ) : Commute (u ^ a) (v ^ b) :=
  (show Commute u v from h).pow_pow a b

/-- Pull back a `HeisCfg 3 n` configuration along a group isomorphism `e : S ≃* G` to obtain a
`RootHeisenbergData` structure over `ZMod 3`. -/
theorem rootHeisenbergData_of_heisCfg {G S : Type*} [Group G] [Group S] {n : ℕ}
    {x y : Fin n → G} {z : G} (e : S ≃* G)
    (h : HeisCfg 3 n x y z) (hy : ∀ i, y i ^ 3 = 1) :
    RootHeisenbergData (fun i (a : ZMod 3) => e.symm (x i ^ a.val))
      (fun i (b : ZMod 3) => e.symm (y i ^ b.val))
      (fun (s : ZMod 3) => e.symm (z ^ s.val))
      (fun _ : Fin n => (1 : ZMod 3)) :=
  let f := e.symm.toMonoidHom
  have hf : Function.Injective f := e.symm.injective
  { x_add := fun i a b => by rw [pow_val_add (h.xp i), map_mul]
    y_add := fun i a b => by rw [pow_val_add (hy i), map_mul]
    z_add := fun a b => by rw [pow_val_add h.zp, map_mul]
    z_eq_one := fun a ha => by
      have h1 : z ^ a.val = z ^ (0 : ZMod 3).val := by
        rw [ZMod.val_zero, pow_zero]
        exact hf (ha.trans (map_one f).symm)
      exact zpow_val_inj (orderOf_z h) h1
    c_ne_zero := fun _ => one_ne_zero
    commute_x_x := fun i j a b => (comm_pow_of_comm (h.xx i j) a.val b.val).map f
    commute_y_y := fun i j a b => by
      by_cases hij : i = j
      · subst hij
        exact ((Commute.refl (y i)).pow_pow a.val b.val).map f
      · exact (comm_pow_of_comm (h.yy i j hij) a.val b.val).map f
    commute_x_z := fun i a b => (comm_pow_of_comm (h.zx i) a.val b.val).map f
    commute_y_z := fun i a b => (comm_pow_of_comm (h.zy i) a.val b.val).map f
    commute_x_y_of_ne := fun i j hij a b => (comm_pow_of_comm (h.xy i j hij) a.val b.val).map f
    comm_x_y := fun i a b => by
      rw [← map_commutatorElement e.symm]
      congr 1
      have hzy : Commute z (y i) := (h.zy i).symm
      have hzx : Commute z (x i) := (h.zx i).symm
      have hmul := pow_mul_pow_of_mul_eq (heisCfg_xy_same h i) hzy hzx a.val b.val
      have hcomm := comm_eq_of_mul_eq ((hzx.pow_left _).pow_right _)
        ((hzy.pow_left _).pow_right _) hmul
      rw [commutatorElement_def, hcomm, ← pow_val_mul h.zp a b, one_mul] }

/-- Every proper subgroup of `Fi₂₃` has index at least `230` (in fact at least `243`). -/
theorem index_ge_Fi23 {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .Fi23) {H : Subgroup S} (hH : H ≠ ⊤) :
    230 ≤ H.index := by
  obtain ⟨x, y, z, h, hy⟩ := Certificates.certificate129030
  have R := @rootHeisenbergData_of_heisCfg NativeSporadic.Fi23 S Units.instGroup _ 4 x y z e h hy
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h243 : 3 * Nat.card (ZMod 3) ^ 4 ≤ H.index :=
    R.mul_pow_le_index_of_ne_top (p := 3) hH
  rw [Nat.card_zmod] at h243
  omega

/-- Maróti's bound for primitive almost simple groups with socle `Fi₂₃`. -/
theorem sporadicCase_Fi23 {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type) [Group S]
    [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .Fi23)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 4089470473293004800 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_Fi23
  have hout : Nat.card (OuterAut S) ∣ 1 := by
    change Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ∣ 1
    have eqv := @CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      S NativeSporadic.Fi23 _ Units.instGroup e
    rw [Nat.card_congr eqv.toEquiv, card_outer_fi23]
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 230) (c := 1) (by decide)
    (fun H hH => index_ge_Fi23 e hH) hout ?_
  rw [hcard]
  decide

end Maroti
