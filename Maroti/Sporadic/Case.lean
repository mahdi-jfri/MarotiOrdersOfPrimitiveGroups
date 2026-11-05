module

public import Maroti.Interface
import Maroti.Sporadic.Mathieu
import Maroti.Sporadic.MathieuM12
import Maroti.Sporadic.MathieuM12M22
import Maroti.Sporadic.MathieuM23M24
import Maroti.Sporadic.J1BM
import Maroti.Sporadic.J2
import Maroti.Sporadic.J3
import Maroti.Sporadic.J4
import Maroti.Sporadic.Co1
import Maroti.Sporadic.Co2
import Maroti.Sporadic.Co3
import Maroti.Sporadic.Fi22
import Maroti.Sporadic.Fi23
import Maroti.Sporadic.Fi24
import Maroti.Sporadic.HS
import Maroti.Sporadic.McL
import Maroti.Sporadic.He
import Maroti.Sporadic.Ru
import Maroti.Sporadic.Suz
import Maroti.Sporadic.ONan
import Maroti.Sporadic.HN
import Maroti.Sporadic.Ly
import Maroti.Sporadic.Th

/-!
# Sporadic Simple Groups Case of Maróti's Theorem

This file assembles the sporadic socle case of Theorem 1.1 of Maróti (Section 2, Step 2,
page 634) by dispatching over the 26 sporadic simple groups `s : TauCeti.SporadicName` in
`CFSG.Blueprint.NativeSporadic.Carrier` to the per-group theorems `sporadicCase_<s>`.
-/

@[expose] public section

namespace Maroti

open CFSG.Blueprint

/-- Theorem 1.1 of Maróti (2002) for primitive almost simple groups with sporadic socle,
given the cases `J₃` and `Ru`. -/
theorem sporadicCase_of_J3_Ru
    (hJ3 : ∀ {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type) [Group S]
      [MulAction.IsPreprimitive G α], IsAlmostSimpleWith G S →
      Nonempty (S ≃* NativeSporadic.Carrier .J3) → Nat.card G ≤ bound (Nat.card α))
    (hRu : ∀ {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type) [Group S]
      [MulAction.IsPreprimitive G α], IsAlmostSimpleWith G S →
      Nonempty (S ≃* NativeSporadic.Carrier .Ru) → Nat.card G ≤ bound (Nat.card α)) :
    AlmostSimpleCase SporadicSocle := by
  intro α _ G S _ _ hS ⟨s, he⟩
  cases s with
  | M11 => exact sporadicCase_M11 G S hS he
  | M12 => exact sporadicCase_M12 G S hS he
  | M22 => exact sporadicCase_M22 G S hS he
  | M23 => exact sporadicCase_M23 G S hS he
  | M24 => exact sporadicCase_M24 G S hS he
  | J1 => exact Or.inr (Or.inr (sporadicCase_J1 G S hS he))
  | J2 => exact Or.inr (Or.inr (sporadicCase_J2 G S hS he))
  | J3 => exact Or.inr (Or.inr (hJ3 G S hS he))
  | J4 => exact Or.inr (Or.inr (sporadicCase_J4 G S hS he))
  | Co1 => exact Or.inr (Or.inr (sporadicCase_Co1 G S hS he))
  | Co2 => exact Or.inr (Or.inr (sporadicCase_Co2 G S hS he))
  | Co3 => exact Or.inr (Or.inr (sporadicCase_Co3 G S hS he))
  | Fi22 => exact Or.inr (Or.inr (sporadicCase_Fi22 G S hS he))
  | Fi23 => exact Or.inr (Or.inr (sporadicCase_Fi23 G S hS he))
  | Fi24Prime => exact Or.inr (Or.inr (sporadicCase_Fi24Prime G S hS he))
  | HS => exact Or.inr (Or.inr (sporadicCase_HS G S hS he))
  | McL => exact Or.inr (Or.inr (sporadicCase_McL G S hS he))
  | He => exact Or.inr (Or.inr (sporadicCase_He G S hS he))
  | Ru => exact Or.inr (Or.inr (hRu G S hS he))
  | Suz => exact Or.inr (Or.inr (sporadicCase_Suz G S hS he))
  | ONan => exact Or.inr (Or.inr (sporadicCase_ONan G S hS he))
  | HN => exact Or.inr (Or.inr (sporadicCase_HN G S hS he))
  | Ly => exact Or.inr (Or.inr (sporadicCase_Ly G S hS he))
  | Th => exact Or.inr (Or.inr (sporadicCase_Th G S hS he))
  | B => exact Or.inr (Or.inr (sporadicCase_B G S hS he))
  | M => exact Or.inr (Or.inr (sporadicCase_M G S hS he))

/-- Theorem 1.1 of Maróti (Section 2, Step 2, page 634) for primitive almost simple groups with
sporadic socle. -/
theorem sporadicCase : AlmostSimpleCase SporadicSocle :=
  sporadicCase_of_J3_Ru (@sporadicCase_J3) (@sporadicCase_Ru)

end Maroti
