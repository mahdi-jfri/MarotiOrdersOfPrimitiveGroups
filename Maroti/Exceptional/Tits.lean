module

public import Maroti.Exceptional.AutBound
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.SignalizerFunctorTheorem.CatalogBridge.TitsDerived

/-!
# The Tits Group Case of Maróti's Theorem

This file proves that every proper subgroup of the Tits simple group `²F₄(2)'` has index at least
`32`, using the `2^(1+8)` Heisenberg subgroup inside the derived subgroup of `²F₄(2)` from
`CFSG.SignalizerFunctorTheorem.CatalogBridge.titsD_action_trivial`, and deduces
`|G| ≤ bound |α|` for any primitive almost simple group `G ≤ Perm α` with Tits socle
(Maróti, Section 2, Step 2, pages 634–635, and Tits, *Algebraic and abstract simple groups*,
Ann. of Math. (2) 80 (1964), 313–329).
-/

@[expose] public section

namespace Maroti

open CFSG.Blueprint CFSG.LieType.Ree
open CFSG.Sporadic.Schreier.Tits (titsModelEquiv titsDerivedIso)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (titsD_action_trivial)

/-- Every proper subgroup `H` of a Tits group model `S` (`²F₄(2)'`) has index at least `32`. -/
theorem index_ge_of_reeTitsModel_Tits {S : Type} [Group S] {p f : ℕ}
    (h : ReeTitsModel S .Tits p f) (H : Subgroup S) (hH : H ≠ ⊤) :
    32 ≤ H.index := by
  obtain ⟨e₁⟩ := titsModelEquiv S p f h
  let e : S ≃* ↥(commutator (reeFixed ReeTag.F4 (ZMod 2) 0)) :=
    e₁.trans (titsDerivedIso (K := ZMod 2)).symm
  have : Finite S := Nat.finite_of_card_ne_zero (by rw [(card_reeTitsModel_Tits h).1]; decide)
  by_contra! hlt
  rw [Subgroup.index_eq_card] at hlt
  let π : ↥(commutator (reeFixed ReeTag.F4 (ZMod 2) 0)) →* Equiv.Perm (S ⧸ H) :=
    (MulAction.toPermHom S (S ⧸ H)).comp e.symm.toMonoidHom
  have htriv := titsD_action_trivial (Nat.card_zmod 2) hlt π
  apply hH
  rw [Subgroup.eq_top_iff']
  intro s
  have hs := congrArg (fun σ : Equiv.Perm (S ⧸ H) => σ (QuotientGroup.mk (1 : S))) (htriv (e s))
  simp only [π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
    MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq] at hs
  have hs' := QuotientGroup.leftRel_apply.mp (Quotient.exact hs)
  simpa using hs'

/-- For the Tits simple group `S`, `|S| · |Out(S)| = 17971200 · 2 ≤ bound 32`. -/
theorem card_mul_outerAut_le_bound_of_reeTitsModel_Tits {S : Type} [Group S] {p f : ℕ}
    (h : ReeTitsModel S .Tits p f) :
    Nat.card S * 2 ≤ bound 32 := by
  rw [(card_reeTitsModel_Tits h).1]
  decide

/-- Any primitive almost simple group `G ≤ Perm α` whose socle is the Tits group `²F₄(2)'`
satisfies `|G| ≤ bound |α|`. -/
theorem card_le_bound_of_reeTitsModel_Tits {α : Type} [Finite α]
    {G : Subgroup (Equiv.Perm α)} [MulAction.IsPreprimitive G α]
    {S : Type} [Group S] {p f : ℕ} (hAS : IsAlmostSimpleWith G S)
    (h : ReeTitsModel S .Tits p f) :
    Nat.card G ≤ bound (Nat.card α) :=
  hAS.card_le_bound_of_outerAut_le (index_ge_of_reeTitsModel_Tits h)
    (card_reeTitsModel_Tits h).2.le (card_mul_outerAut_le_bound_of_reeTitsModel_Tits h)

end Maroti
