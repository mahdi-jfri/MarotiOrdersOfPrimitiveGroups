module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.AutSix
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Maroti.Interface

/-!
# Automorphism bound for alternating socles

This file proves `Maroti.autBound_alternating : AutBound AlternatingSocle`, stating that for any
finite group `S` isomorphic to `alternatingGroup (Fin m)` with `5 ≤ m`, its automorphism group
`MulAut S` satisfies `Nat.card (MulAut S) ≤ Nat.card S ^ 2` (Maróti, Section 2, Step 1, page 634).

For `m = 6`, the theorem
`CFSG.HardMathSupport.Timmesfeld.Balance.Alt.finite_and_card_mulAut_alternatingGroup_six_le`
(`CFSG/HardMathSupport/Timmesfeld/Balance/Alt/AutSix.lean`) shows that
`MulAut (alternatingGroup (Fin 6))` is finite of cardinality at most `1440 ≤ 360 ^ 2`.
For `m ≥ 5` with `m ≠ 6`, the theorem
`CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj`
(`CFSG/ThirdParty/QiuzhenCFSG/Theory/AutAlternating.lean`) gives a bijection between
`Equiv.Perm (Fin m)` and `MulAut (alternatingGroup (Fin m))`, so
`Nat.card (MulAut (alternatingGroup (Fin m))) = m! ≤ (m! / 2) ^ 2`.
-/

@[expose] public section

namespace Maroti

open Equiv Subgroup
open scoped Nat

/-- For `m ≥ 5` and `m ≠ 6`, `MulAut.conjNormal` gives a multiplicative equivalence between
`Equiv.Perm (Fin m)` and `MulAut (alternatingGroup (Fin m))`. -/
noncomputable def permMulEquivMulAutAlternating {m : ℕ} (hm : 5 ≤ m) (hm6 : m ≠ 6) :
    Perm (Fin m) ≃* MulAut (alternatingGroup (Fin m)) :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin m)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm hm6)

/-- For `m ≥ 2`, the cardinality of `alternatingGroup (Fin m)` is `m! / 2`. -/
theorem nat_card_alternatingGroup_fin {m : ℕ} (hm : 2 ≤ m) :
    Nat.card (alternatingGroup (Fin m)) = m ! / 2 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  have h := two_mul_card_alternatingGroup (α := Fin m)
  rw [Fintype.card_perm, Fintype.card_fin] at h
  rw [Nat.card_eq_fintype_card]
  omega

/-- For `m ≥ 4`, `m! ≤ (m! / 2) ^ 2`. -/
private theorem factorial_le_half_factorial_sq {m : ℕ} (hm : 4 ≤ m) :
    m ! ≤ (m ! / 2) ^ 2 := by
  have h24 : 24 ≤ m ! := by
    calc 24 = 4 ! := by decide
      _ ≤ m ! := Nat.factorial_le hm
  have hdvd : 2 ∣ m ! := Nat.dvd_factorial (by decide) (by omega)
  obtain ⟨k, hk⟩ := hdvd
  have hk_eq : m ! / 2 = k := by omega
  rw [hk_eq, sq]
  have hk12 : 12 ≤ k := by omega
  nlinarith

/-- For any finite group `S` with `AlternatingSocle S` (`S ≃* alternatingGroup (Fin m)` for some
`m ≥ 5`), `Nat.card (MulAut S) ≤ Nat.card S ^ 2` (Maróti, Section 2, Step 1, page 634). -/
theorem autBound_alternating : AutBound AlternatingSocle := by
  rintro S _ _ ⟨m, hm, ⟨e⟩⟩
  have hcongr : MulAut S ≃* MulAut (alternatingGroup (Fin m)) := MulAut.congr e
  have hcard_S : Nat.card S = m ! / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup_fin (by omega)]
  by_cases hm6 : m = 6
  · subst hm6
    obtain ⟨_, hle⟩ :=
      CFSG.HardMathSupport.Timmesfeld.Balance.Alt.finite_and_card_mulAut_alternatingGroup_six_le
    rw [Nat.card_congr hcongr.toEquiv, hcard_S]
    exact hle.trans (by decide)
  · let eAut := (permMulEquivMulAutAlternating hm hm6).trans hcongr.symm
    rw [← Nat.card_congr eAut.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin, hcard_S]
    exact factorial_le_half_factorial_sq (by omega)

end Maroti
