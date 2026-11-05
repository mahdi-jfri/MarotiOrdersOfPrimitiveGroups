module

public import Maroti.AlmostSimple.Basic
public import CFSG.Open.Defs
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.ClassicalInvolution.Orders.Twisted
import CFSG.ClassicalInvolution.Orders.Ree
import CFSG.LieType.Ree.SuzukiOrder
import CFSG.RankThree.SteinbergR3ELargeReeOrder
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
import CFSG.LieType.Chevalley.TwistedE6OuterOrder
import CFSG.LieType.Suzuki.SuzukiOuterCyclic
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter
import CFSG.Sporadic.Schreier.TitsOuterTwo

/-!
# Orders and Outer Automorphism Bounds for Exceptional Groups of Lie Type

This file proves the order formulas, polynomial upper bounds on `|S|`, and outer automorphism
bounds `|Out(S)|` for all exceptional simple groups of Lie type (`ExceptionalSocle`), and deduces
`Maroti.autBound_exceptional : AutBound ExceptionalSocle`, that is, `|Aut(S)| ≤ |S|²` for every
finite exceptional group of Lie type `S` (Maróti, Section 2, Step 1, page 634).

The order formulas and outer automorphism group structures follow Carter, *Simple Groups of Lie
Type* (1972), Theorem 9.4.10 and Section 12.5, and Gorenstein–Lyons–Solomon, *The Classification of
the Finite Simple Groups*, Number 3 (1998), Theorem 2.5.12.
-/

@[expose] public section

namespace Maroti

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.ComponentClassification.UnbalancedCatalog
  (even_G2_exact_automorphism_normal_form large_Ree_model_field_outer_group_and_inner_involutions)
open CFSG.LieType.Ree (ReeTag small_Ree_model_Schreier suzuki_order)
open CFSG.ComponentClassification.LiteratureLocal.SmallRee (outer_reeGamma_cyclic)

/-! ### Polynomial bounds on the order functions -/

/-- For any `b ≤ a` and `q : ℕ`, `(q ^ a + 1) * (q ^ b - 1) ≤ q ^ (a + b)`. -/
theorem add_one_mul_sub_one_le_pow {a b : ℕ} (ha : b ≤ a) (q : ℕ) :
    (q ^ a + 1) * (q ^ b - 1) ≤ q ^ (a + b) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rcases eq_or_ne b 0 with rfl | hb0
    · simp
    · simp [zero_pow hb0]
  · have hq1 : 1 ≤ q := Nat.pos_of_ne_zero hq0
    have hqb : 1 ≤ q ^ b := Nat.one_le_pow b q hq1
    have hba : q ^ b ≤ q ^ a := Nat.pow_le_pow_right hq1 ha
    zify [hqb]
    have hba' : (q : ℤ) ^ b ≤ (q : ℤ) ^ a := by exact_mod_cast hba
    have h1 : (q : ℤ) ^ a * (q : ℤ) ^ b = (q : ℤ) ^ (a + b) := by rw [pow_add]
    linarith

/-- Upper bound `ordG2 q ≤ q ^ 14`. -/
theorem ordG2_le_pow (q : ℕ) : ordG2 q ≤ q ^ 14 := by
  unfold ordG2
  calc q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)
      ≤ q ^ 6 * q ^ 6 * q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 14 := by ring

/-- Upper bound `ordF4 q ≤ q ^ 52`. -/
theorem ordF4_le_pow (q : ℕ) : ordF4 q ≤ q ^ 52 := by
  unfold ordF4
  calc q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
      ≤ q ^ 24 * q ^ 12 * q ^ 8 * q ^ 6 * q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 52 := by ring

/-- Upper bound `ordE6 q ≤ q ^ 78`. -/
theorem ordE6_le_pow (q : ℕ) : ordE6 q ≤ q ^ 78 := by
  unfold ordE6
  refine (Nat.div_le_self _ _).trans ?_
  calc q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1)
      ≤ q ^ 36 * q ^ 12 * q ^ 9 * q ^ 8 * q ^ 6 * q ^ 5 * q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 78 := by ring

/-- Upper bound `ordTwistedE6 q ≤ q ^ 78`. -/
theorem ordTwistedE6_le_pow (q : ℕ) : ordTwistedE6 q ≤ q ^ 78 := by
  unfold ordTwistedE6
  refine (Nat.div_le_self _ _).trans ?_
  have h98 : (q ^ 9 + 1) * (q ^ 8 - 1) ≤ q ^ 17 := add_one_mul_sub_one_le_pow (by decide) q
  have h52 : (q ^ 5 + 1) * (q ^ 2 - 1) ≤ q ^ 7 := add_one_mul_sub_one_le_pow (by decide) q
  calc q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)
      = q ^ 36 * (q ^ 12 - 1) * ((q ^ 9 + 1) * (q ^ 8 - 1)) * (q ^ 6 - 1) *
          ((q ^ 5 + 1) * (q ^ 2 - 1)) := by ring
    _ ≤ q ^ 36 * q ^ 12 * q ^ 17 * q ^ 6 * q ^ 7 := by
        gcongr
        · exact Nat.sub_le _ _
        · exact Nat.sub_le _ _
    _ = q ^ 78 := by ring

/-- Upper bound `ordE7 q ≤ q ^ 133`. -/
theorem ordE7_le_pow (q : ℕ) : ordE7 q ≤ q ^ 133 := by
  unfold ordE7
  refine (Nat.div_le_self _ _).trans ?_
  calc q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 2 - 1)
      ≤ q ^ 63 * q ^ 18 * q ^ 14 * q ^ 12 * q ^ 10 * q ^ 8 * q ^ 6 * q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 133 := by ring

/-- Upper bound `ordE8 q ≤ q ^ 248`. -/
theorem ordE8_le_pow (q : ℕ) : ordE8 q ≤ q ^ 248 := by
  unfold ordE8
  calc q ^ 120 * (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
        (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)
      ≤ q ^ 120 * q ^ 30 * q ^ 24 * q ^ 20 * q ^ 18 * q ^ 14 * q ^ 12 * q ^ 8 * q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 248 := by ring

/-- Upper bound `ordTrialityD4 q ≤ q ^ 28`. -/
theorem ordTrialityD4_le_pow (q : ℕ) : ordTrialityD4 q ≤ q ^ 28 := by
  unfold ordTrialityD4
  have h84 : (q ^ 8 + q ^ 4 + 1) * (q ^ 2 - 1) ≤ q ^ 10 := by
    rcases eq_or_ne q 0 with rfl | hq0
    · simp
    · have hq1 : 1 ≤ q := Nat.pos_of_ne_zero hq0
      have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q hq1
      have h24 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right hq1 (by decide)
      have h68 : q ^ 6 ≤ q ^ 8 := Nat.pow_le_pow_right hq1 (by decide)
      zify [hq2]
      have h24' : (q : ℤ) ^ 2 ≤ (q : ℤ) ^ 4 := by exact_mod_cast h24
      have h68' : (q : ℤ) ^ 6 ≤ (q : ℤ) ^ 8 := by exact_mod_cast h68
      linarith
  calc q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
      = q ^ 12 * ((q ^ 8 + q ^ 4 + 1) * (q ^ 2 - 1)) * (q ^ 6 - 1) := by ring
    _ ≤ q ^ 12 * q ^ 10 * q ^ 6 := by
        gcongr
        exact Nat.sub_le _ _
    _ = q ^ 28 := by ring

/-- Upper bound `ordSuzuki q ≤ q ^ 5`. -/
theorem ordSuzuki_le_pow (q : ℕ) : ordSuzuki q ≤ q ^ 5 := by
  unfold ordSuzuki
  have h21 : (q ^ 2 + 1) * (q - 1) ≤ q ^ 3 := by
    simpa using add_one_mul_sub_one_le_pow (a := 2) (b := 1) (by decide) q
  calc q ^ 2 * (q ^ 2 + 1) * (q - 1)
      = q ^ 2 * ((q ^ 2 + 1) * (q - 1)) := by ring
    _ ≤ q ^ 2 * q ^ 3 := Nat.mul_le_mul_left _ h21
    _ = q ^ 5 := by ring

/-- Upper bound `ordRee q ≤ q ^ 7`. -/
theorem ordRee_le_pow (q : ℕ) : ordRee q ≤ q ^ 7 := by
  unfold ordRee
  have h31 : (q ^ 3 + 1) * (q - 1) ≤ q ^ 4 := by
    simpa using add_one_mul_sub_one_le_pow (a := 3) (b := 1) (by decide) q
  calc q ^ 3 * (q ^ 3 + 1) * (q - 1)
      = q ^ 3 * ((q ^ 3 + 1) * (q - 1)) := by ring
    _ ≤ q ^ 3 * q ^ 4 := Nat.mul_le_mul_left _ h31
    _ = q ^ 7 := by ring

/-- Upper bound `ordTwistedF4 q ≤ q ^ 26`. -/
theorem ordTwistedF4_le_pow (q : ℕ) : ordTwistedF4 q ≤ q ^ 26 := by
  unfold ordTwistedF4
  have h64 : (q ^ 6 + 1) * (q ^ 4 - 1) ≤ q ^ 10 := add_one_mul_sub_one_le_pow (by decide) q
  have h31 : (q ^ 3 + 1) * (q - 1) ≤ q ^ 4 := by
    simpa using add_one_mul_sub_one_le_pow (a := 3) (b := 1) (by decide) q
  calc q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)
      = q ^ 12 * ((q ^ 6 + 1) * (q ^ 4 - 1)) * ((q ^ 3 + 1) * (q - 1)) := by ring
    _ ≤ q ^ 12 * q ^ 10 * q ^ 4 := by gcongr
    _ = q ^ 26 := by ring

/-! ### Lower bounds on the order functions -/

/-- For `2 ≤ q` and `6 ≤ a`, `6 * q ≤ q ^ a`. -/
private theorem six_mul_le_pow {q a : ℕ} (hq : 2 ≤ q) (ha : 6 ≤ a) : 6 * q ≤ q ^ a := by
  obtain ⟨d, rfl⟩ : ∃ d, a = 5 + (d + 1) := ⟨a - 6, by omega⟩
  calc 6 * q ≤ 2 ^ 5 * q ^ 1 := by
        rw [pow_one]
        exact Nat.mul_le_mul_right q (by decide)
    _ ≤ q ^ 5 * q ^ (d + 1) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hq 5) (Nat.pow_le_pow_right (by omega) (by omega))
    _ = q ^ (5 + (d + 1)) := (pow_add q 5 (d + 1)).symm

/-- For `2 ≤ q`, `6 * q ≤ ordG2 q`. -/
theorem six_mul_le_ordG2 {q : ℕ} (hq : 2 ≤ q) : 6 * q ≤ ordG2 q := by
  unfold ordG2
  have hq2 : 1 ≤ q ^ 2 - 1 := by
    have : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    omega
  have hq6 : 1 ≤ q ^ 6 - 1 := by
    have : 2 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
    omega
  calc 6 * q ≤ q ^ 6 := six_mul_le_pow hq (by decide)
    _ = q ^ 6 * 1 * 1 := by ring
    _ ≤ q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) := by gcongr

/-- For `2 ≤ q`, `6 * q ≤ ordF4 q`. -/
theorem six_mul_le_ordF4 {q : ℕ} (hq : 2 ≤ q) : 6 * q ≤ ordF4 q := by
  unfold ordF4
  have hpos : ∀ k, 1 ≤ k → 1 ≤ q ^ k - 1 := fun k hk => by
    have : 2 ^ 1 ≤ q ^ k := (Nat.pow_le_pow_left hq 1).trans (Nat.pow_le_pow_right (by omega) hk)
    omega
  calc 6 * q ≤ q ^ 24 := six_mul_le_pow hq (by decide)
    _ = q ^ 24 * 1 * 1 * 1 * 1 := by ring
    _ ≤ q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) := by
        gcongr <;> exact hpos _ (by decide)

/-- For `2 ≤ q`, `6 * q ≤ ordE6 q`. -/
theorem six_mul_le_ordE6 {q : ℕ} (hq : 2 ≤ q) : 6 * q ≤ ordE6 q := by
  unfold ordE6
  have hpos : ∀ k, 1 ≤ k → 1 ≤ q ^ k - 1 := fun k hk => by
    have : 2 ^ 1 ≤ q ^ k := (Nat.pow_le_pow_left hq 1).trans (Nat.pow_le_pow_right (by omega) hk)
    omega
  have hq2 : 3 ≤ q ^ 2 - 1 := by
    have : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    omega
  have hg : Nat.gcd 3 (q - 1) ≤ 3 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left 3 (q - 1))
  have hnum : q ^ 36 * 3 ≤
      q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
        (q ^ 2 - 1) := by
    calc q ^ 36 * 3 = q ^ 36 * 1 * 1 * 1 * 1 * 1 * 3 := by ring
      _ ≤ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
            (q ^ 2 - 1) := by
          gcongr
          all_goals exact hpos _ (by decide)
  refine (six_mul_le_pow hq (by decide : 6 ≤ 36)).trans ?_
  rw [Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_left _ (by decide))]
  exact (Nat.mul_le_mul_left (q ^ 36) hg).trans hnum

/-- For `2 ≤ q`, `6 * q ≤ ordTwistedE6 q`. -/
theorem six_mul_le_ordTwistedE6 {q : ℕ} (hq : 2 ≤ q) : 6 * q ≤ ordTwistedE6 q := by
  unfold ordTwistedE6
  have hpos : ∀ k, 1 ≤ k → 1 ≤ q ^ k - 1 := fun k hk => by
    have : 2 ^ 1 ≤ q ^ k := (Nat.pow_le_pow_left hq 1).trans (Nat.pow_le_pow_right (by omega) hk)
    omega
  have hq2 : 3 ≤ q ^ 2 - 1 := by
    have : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    omega
  have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left 3 (q + 1))
  have hnum : q ^ 36 * 3 ≤
      q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
        (q ^ 2 - 1) := by
    calc q ^ 36 * 3 = q ^ 36 * 1 * 1 * 1 * 1 * 1 * 3 := by ring
      _ ≤ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
            (q ^ 2 - 1) := by
          gcongr
          · exact hpos _ (by decide)
          · omega
          · exact hpos _ (by decide)
          · exact hpos _ (by decide)
          · omega
  refine (six_mul_le_pow hq (by decide : 6 ≤ 36)).trans ?_
  rw [Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_left _ (by decide))]
  exact (Nat.mul_le_mul_left (q ^ 36) hg).trans hnum

/-- For `2 ≤ q`, `6 * q ≤ ordE7 q`. -/
theorem six_mul_le_ordE7 {q : ℕ} (hq : 2 ≤ q) : 6 * q ≤ ordE7 q := by
  unfold ordE7
  have hpos : ∀ k, 1 ≤ k → 1 ≤ q ^ k - 1 := fun k hk => by
    have : 2 ^ 1 ≤ q ^ k := (Nat.pow_le_pow_left hq 1).trans (Nat.pow_le_pow_right (by omega) hk)
    omega
  have hq2 : 2 ≤ q ^ 2 - 1 := by
    have : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    omega
  have hg : Nat.gcd 2 (q - 1) ≤ 2 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left 2 (q - 1))
  have hnum : q ^ 63 * 2 ≤
      q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 2 - 1) := by
    calc q ^ 63 * 2 = q ^ 63 * 1 * 1 * 1 * 1 * 1 * 1 * 2 := by ring
      _ ≤ q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
            (q ^ 6 - 1) * (q ^ 2 - 1) := by
          gcongr
          all_goals exact hpos _ (by decide)
  refine (six_mul_le_pow hq (by decide : 6 ≤ 63)).trans ?_
  rw [Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_left _ (by decide))]
  exact (Nat.mul_le_mul_left (q ^ 63) hg).trans hnum

/-- For `2 ≤ q`, `6 * q ≤ ordE8 q`. -/
theorem six_mul_le_ordE8 {q : ℕ} (hq : 2 ≤ q) : 6 * q ≤ ordE8 q := by
  unfold ordE8
  have hpos : ∀ k, 1 ≤ k → 1 ≤ q ^ k - 1 := fun k hk => by
    have : 2 ^ 1 ≤ q ^ k := (Nat.pow_le_pow_left hq 1).trans (Nat.pow_le_pow_right (by omega) hk)
    omega
  calc 6 * q ≤ q ^ 120 := six_mul_le_pow hq (by decide)
    _ = q ^ 120 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 := by ring
    _ ≤ q ^ 120 * (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
          (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1) := by
        gcongr <;> exact hpos _ (by decide)

/-- For `2 ≤ q`, `6 * q ≤ ordTrialityD4 q`. -/
theorem six_mul_le_ordTrialityD4 {q : ℕ} (hq : 2 ≤ q) : 6 * q ≤ ordTrialityD4 q := by
  unfold ordTrialityD4
  have hpos : ∀ k, 1 ≤ k → 1 ≤ q ^ k - 1 := fun k hk => by
    have : 2 ^ 1 ≤ q ^ k := (Nat.pow_le_pow_left hq 1).trans (Nat.pow_le_pow_right (by omega) hk)
    omega
  calc 6 * q ≤ q ^ 12 := six_mul_le_pow hq (by decide)
    _ = q ^ 12 * 1 * 1 * 1 := by ring
    _ ≤ q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) := by
        gcongr
        · omega
        · exact hpos _ (by decide)
        · exact hpos _ (by decide)

/-- For `2 ≤ q`, `q ≤ ordSuzuki q`. -/
theorem self_le_ordSuzuki {q : ℕ} (hq : 2 ≤ q) : q ≤ ordSuzuki q := by
  unfold ordSuzuki
  have h1 : 1 ≤ q ^ 2 + 1 := by omega
  have h2 : 1 ≤ q - 1 := by omega
  calc q ≤ q ^ 2 := Nat.le_self_pow (by decide) q
    _ = q ^ 2 * 1 * 1 := by ring
    _ ≤ q ^ 2 * (q ^ 2 + 1) * (q - 1) := by gcongr

/-- For `2 ≤ q`, `q ≤ ordRee q`. -/
theorem self_le_ordRee {q : ℕ} (hq : 2 ≤ q) : q ≤ ordRee q := by
  unfold ordRee
  have h1 : 1 ≤ q ^ 3 + 1 := by omega
  have h2 : 1 ≤ q - 1 := by omega
  calc q ≤ q ^ 3 := Nat.le_self_pow (by decide) q
    _ = q ^ 3 * 1 * 1 := by ring
    _ ≤ q ^ 3 * (q ^ 3 + 1) * (q - 1) := by gcongr

/-- For `2 ≤ q`, `q ≤ ordTwistedF4 q`. -/
theorem self_le_ordTwistedF4 {q : ℕ} (hq : 2 ≤ q) : q ≤ ordTwistedF4 q := by
  unfold ordTwistedF4
  have hq4 : 1 ≤ q ^ 4 - 1 := by
    have : 2 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    omega
  have hq1 : 1 ≤ q - 1 := by omega
  calc q ≤ q ^ 12 := Nat.le_self_pow (by decide) q
    _ = q ^ 12 * 1 * 1 * 1 * 1 := by ring
    _ ≤ q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) := by
        gcongr <;> omega

/-! ### Exact orders of exceptional models -/

/-- Exact order of a Chevalley exceptional model `G` (`G₂, F₄, E₆, E₇, E₈, ²E₆, ³D₄`). -/
theorem card_chevalleyExceptionalModel {G : Type} [Group G] {t : StatedLieTag} {p f : ℕ}
    (h : ChevalleyExceptionalModel G t p f) :
    Nat.card G = match t with
      | .G2 => ordG2 (p ^ f) | .F4 => ordF4 (p ^ f) | .E6 => ordE6 (p ^ f)
      | .E7 => ordE7 (p ^ f) | .E8 => ordE8 (p ^ f) | .twistedE6 => ordTwistedE6 (p ^ f)
      | .trialityD4 => ordTrialityD4 (p ^ f) | _ => 0 := by
  rcases eq_or_ne p 2 with rfl | hp2
  · cases t <;> exact CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  · cases t <;> exact CFSG.ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two hp2 h

/-- Exact order of a Suzuki model `G` (`²B₂(2^f)` with `f = 2a + 1 ≥ 3`). -/
theorem card_suzukiModel {G : Type} [Group G] {p f : ℕ} (h : SuzukiModel G p f) :
    p = 2 ∧ (∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1) ∧ Nat.card G = ordSuzuki (2 ^ f) := by
  obtain ⟨rfl, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  refine ⟨rfl, ⟨a, ha, rfl⟩, ?_⟩
  rw [Nat.card_congr e.toEquiv, suzuki_order hK, ordSuzuki]
  ring

/-- Exact order of a small Ree model `G` (`²G₂(3^f)` with `f = 2a + 1 ≥ 3`). -/
theorem card_reeTitsModel_twistedG2 {G : Type} [Group G] {p f : ℕ}
    (h : ReeTitsModel G .twistedG2 p f) :
    p = 3 ∧ (∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1) ∧ Nat.card G = ordRee (3 ^ f) := by
  obtain ⟨hp, a, ha, hfa, hcard⟩ := CFSG.ClassicalInvolution.card_of_reeTitsModel_twistedG2 h
  exact ⟨hp, ⟨a, ha, hfa⟩, hcard⟩

/-- Exact order of a large Ree model `G` (`²F₄(2^f)` with `f = 2a + 1 ≥ 3`). -/
theorem card_reeTitsModel_twistedF4 {G : Type} [Group G] {p f : ℕ}
    (h : ReeTitsModel G .twistedF4 p f) :
    p = 2 ∧ (∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1) ∧ Nat.card G = ordTwistedF4 (2 ^ f) := by
  have hp : p = 2 := h.1.2.2.2.1
  subst hp
  have hS := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier G 2 f h
  obtain ⟨hadm, a, hfa, K, _, _, hK, ⟨e⟩⟩ := h
  have hf3 : 3 ≤ f := hadm.2.2.2.2.2
  have ha : 1 ≤ a := by omega
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hS.2.2.2.2.2 a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hord :=
    (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
      a K hK').1
  refine ⟨rfl, ⟨a, ha, hfa⟩, ?_⟩
  rw [Nat.card_congr E.toEquiv, hord, ordTwistedF4, hfa]
  set q := 2 ^ (2 * a + 1)
  have h1 : 1 ≤ q := Nat.one_le_two_pow
  have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by decide) q
  have h3 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h3, h4]
  ring

/-- Exact order of a Tits model `G` (`²F₄(2)'`, order `17971200`). -/
theorem card_reeTitsModel_Tits {G : Type} [Group G] {p f : ℕ}
    (h : ReeTitsModel G .Tits p f) :
    Nat.card G = 17971200 ∧ Nat.card (OuterAut G) = 2 := by
  have hT := CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound G p f h
  exact ⟨hT.1, hT.2.2.1⟩

/-! ### Outer automorphism bounds for exceptional models -/

/-- If `e : S ≃* C`, then `Nat.card (OuterAut S) = Nat.card (Outer C)`. -/
private theorem card_outerAut_congr {S C : Type*} [Group S] [Group C] (e : S ≃* C) :
    Nat.card (OuterAut S) = Nat.card (Outer C) :=
  Nat.card_congr (equivalence e).toEquiv

/-- If `Θ : MulAut C →* A` is surjective with `Θ.ker = (MulAut.conj : C →* MulAut C).range`, then
`Nat.card (Outer C) = Nat.card A`. -/
private theorem card_outer_eq_of_surjective_ker_eq_inner {C A : Type*} [Group C] [Group A]
    (Θ : MulAut C →* A) (hsurj : Function.Surjective Θ)
    (hker : Θ.ker = (MulAut.conj : C →* MulAut C).range) :
    Nat.card (Outer C) = Nat.card A := by
  have hker' : inner C = Θ.ker := hker.symm
  have e : Outer C ≃* A :=
    (QuotientGroup.quotientMulEquivOfEq hker').trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)
  exact Nat.card_congr e.toEquiv

/-- For `G₂(p^f)`, `|Out(S)|` divides `2f`, hence `|Out(S)| ≤ 2f`. -/
theorem card_outerAut_G2 {S : Type} [Group S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .G2 p f) :
    Nat.card (OuterAut S) ∣ 2 * f ∧ Nat.card (OuterAut S) ≤ 2 * f := by
  obtain ⟨⟨hp, hf, hadm⟩, hm⟩ := h
  have hm' : UntwistedChevalleyModel S .G2 (p ^ f) := hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm'
  have hdvd : Nat.card (OuterAut S) ∣ 2 * f := by
    rw [card_outerAut_congr e]
    rcases eq_or_ne p 3 with rfl | hp3
    · have : CharP K ReeTag.G2.prime := finite_field_prime_power_characteristic hp hf hK
      obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
      have h2f : NeZero (2 * f) := ⟨by omega⟩
      change Nat.card (Outer (adjointGroup ReeTag.G2.tag K)) ∣ 2 * f
      rw [card_outer_eq_of_surjective_ker_eq_inner Θ hsurj hker,
        Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    · rcases eq_or_ne p 2 with rfl | hp2
      · have hf2 : 2 ≤ f := by
          by_contra hcon
          have : f = 1 := by omega
          subst this
          exact absurd hadm.2 (by norm_num)
        obtain ⟨-, Θ, -, hsurj, hker, -⟩ := even_G2_exact_automorphism_normal_form hf2 K hK
        rw [card_outer_eq_of_surjective_ker_eq_inner Θ hsurj hker,
          (card_ringAut_and_isCyclic hp K hK).1]
        exact dvd_mul_left f 2
      · obtain ⟨-, Θ, -, hsurj, hker, -⟩ :=
          odd_F4_and_nonexceptional_G2_automorphism_normal_form
            hp hp2 hf K hK .G2 (Or.inr ⟨rfl, hp3⟩)
        rw [card_outer_eq_of_surjective_ker_eq_inner Θ hsurj hker,
          (card_ringAut_and_isCyclic hp K hK).1]
        exact dvd_mul_left f 2
  exact ⟨hdvd, Nat.le_of_dvd (by omega) hdvd⟩

/-- For `F₄(p^f)`, `|Out(S)|` divides `2f`, hence `|Out(S)| ≤ 2f`. -/
theorem card_outerAut_F4 {S : Type} [Group S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .F4 p f) :
    Nat.card (OuterAut S) ∣ 2 * f ∧ Nat.card (OuterAut S) ≤ 2 * f := by
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  have hm' : UntwistedChevalleyModel S .F4 (p ^ f) := hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm'
  have hdvd : Nat.card (OuterAut S) ∣ 2 * f := by
    rw [card_outerAut_congr e]
    rcases eq_or_ne p 2 with rfl | hp2
    · have : CharP K ReeTag.F4.prime := finite_field_prime_power_characteristic hp hf hK
      obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
      have h2f : NeZero (2 * f) := ⟨by omega⟩
      change Nat.card (Outer (adjointGroup ReeTag.F4.tag K)) ∣ 2 * f
      rw [card_outer_eq_of_surjective_ker_eq_inner Θ hsurj hker,
        Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    · obtain ⟨-, Θ, -, hsurj, hker, -⟩ :=
        odd_F4_and_nonexceptional_G2_automorphism_normal_form
          hp hp2 hf K hK .F4 (Or.inl rfl)
      rw [card_outer_eq_of_surjective_ker_eq_inner Θ hsurj hker,
        (card_ringAut_and_isCyclic hp K hK).1]
      exact dvd_mul_left f 2
  exact ⟨hdvd, Nat.le_of_dvd (by omega) hdvd⟩

/-- For `E₆(p^f)`, `|Out(S)|` divides `6f`, hence `|Out(S)| ≤ 6f`. -/
theorem card_outerAut_E6 {S : Type} [Group S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .E6 p f) :
    Nat.card (OuterAut S) ∣ 6 * f ∧ Nat.card (OuterAut S) ≤ 6 * f := by
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm
  have hdvd : Nat.card (OuterAut S) ∣ 6 * f := by
    rw [card_outerAut_congr e]
    exact (ordinary_E_outer_order_Cartan_divisor .E6 (Or.inl rfl) hp hf K hK 3 2
      (Or.inl ⟨rfl, rfl, rfl⟩)).1
  exact ⟨hdvd, Nat.le_of_dvd (by omega) hdvd⟩

/-- For `E₇(p^f)`, `|Out(S)|` divides `2f`, hence `|Out(S)| ≤ 2f`. -/
theorem card_outerAut_E7 {S : Type} [Group S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .E7 p f) :
    Nat.card (OuterAut S) ∣ 2 * f ∧ Nat.card (OuterAut S) ≤ 2 * f := by
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 hm
  have hdvd : Nat.card (OuterAut S) ∣ 2 * f := by
    rw [card_outerAut_congr e]
    simpa using (ordinary_E_outer_order_Cartan_divisor .E7 (Or.inr (Or.inl rfl)) hp hf K hK 2 1
      (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))).1
  exact ⟨hdvd, Nat.le_of_dvd (by omega) hdvd⟩

/-- For `E₈(p^f)`, `|Out(S)|` divides `f`, hence `|Out(S)| ≤ f`. -/
theorem card_outerAut_E8 {S : Type} [Group S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .E8 p f) :
    Nat.card (OuterAut S) ∣ f ∧ Nat.card (OuterAut S) ≤ f := by
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 hm
  have hdvd : Nat.card (OuterAut S) ∣ f := by
    rw [card_outerAut_congr e]
    simpa using (ordinary_E_outer_order_Cartan_divisor .E8 (Or.inr (Or.inr rfl)) hp hf K hK 1 1
      (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))).1
  exact ⟨hdvd, Nat.le_of_dvd (by omega) hdvd⟩

/-- For `²E₆(p^f)`, `|Out(S)|` divides `6f`, hence `|Out(S)| ≤ 6f`. -/
theorem card_outerAut_twistedE6 {S : Type} [Group S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .twistedE6 p f) :
    Nat.card (OuterAut S) ∣ 6 * f ∧ Nat.card (OuterAut S) ≤ 6 * f := by
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hp hf hm
  have hdvd : Nat.card (OuterAut S) ∣ 6 * f := by
    rw [card_outerAut_congr e]
    refine (card_outer_twistedE6RootGroup_dvd hp hf K hK σ hσ).trans ?_
    rw [show 6 * f = (2 * 3) * f by ring]
    exact Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_left 2 (Nat.gcd_dvd_left 3 (p ^ f + 1))) f
  exact ⟨hdvd, Nat.le_of_dvd (by omega) hdvd⟩

/-- For `³D₄(p^f)`, `|Out(S)| = 3f`. -/
theorem card_outerAut_trialityD4 {S : Type} [Group S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .trialityD4 p f) :
    Nat.card (OuterAut S) = 3 * f := by
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hm
  rw [card_outerAut_congr e]
  rcases eq_or_ne p 2 with rfl | hp2
  · obtain ⟨-, -, ⟨Θ, -, hsurj, hker, -⟩, -, hcardAut, -⟩ :=
      even_triality_exact_automorphism_normal_form hf K hK σ hσ
    rw [card_outer_eq_of_surjective_ker_eq_inner Θ hsurj hker, hcardAut]
  · obtain ⟨-, -, ⟨Θ, -, hsurj, hker, -⟩, -, hcardAut, -⟩ :=
      odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
    rw [card_outer_eq_of_surjective_ker_eq_inner Θ hsurj hker, hcardAut]

/-- For `²B₂(2^f)`, `|Out(S)|` divides `f`, hence `|Out(S)| ≤ f`. -/
theorem card_outerAut_suzuki {S : Type} [Group S] {p f : ℕ}
    (h : SuzukiModel S p f) :
    Nat.card (OuterAut S) ∣ f ∧ Nat.card (OuterAut S) ≤ f := by
  have hdvd : Nat.card (OuterAut S) ∣ f :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} S p f h).1.2.1
  obtain ⟨-, a, ha, -, -, -, rfl, -⟩ := h
  exact ⟨hdvd, Nat.le_of_dvd (by omega) hdvd⟩

/-- For `²G₂(3^f)`, `|Out(S)| = f`. -/
theorem card_outerAut_twistedG2 {S : Type} [Group S] {p f : ℕ}
    (h : ReeTitsModel S .twistedG2 p f) :
    Nat.card (OuterAut S) = f := by
  obtain ⟨-, -, rfl, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier S p f h
  obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := h
  have ha' : a' = a := by omega
  subst ha'
  have : CharP K ReeTag.G2.prime :=
    finite_field_prime_power_characteristic Nat.prime_three (by omega) hK
  obtain ⟨E⟩ := hiso a' K hfa hK hw
  have hK' : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa]
  rw [card_outerAut_congr E, (outer_reeGamma_cyclic ha hK').2, hfa]

/-- For `²F₄(2^f)`, `|Out(S)| = f`. -/
theorem card_outerAut_twistedF4 {S : Type} [Group S] {p f : ℕ}
    (h : ReeTitsModel S .twistedF4 p f) :
    Nat.card (OuterAut S) = f :=
  (large_Ree_model_field_outer_group_and_inner_involutions S p f h).2.2.2.2.1

/-! ### Automorphism bounds `|Out(S)| ≤ |S|` and `|Aut(S)| ≤ |S|²` for all exceptional groups -/

/-- For every prime `p` and `1 ≤ f`, `f ≤ p ^ f` and `2 ≤ p ^ f`. -/
private theorem exp_le_prime_pow {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) :
    f ≤ p ^ f ∧ 2 ≤ p ^ f := by
  have hp2 : 2 ≤ p := hp.two_le
  refine ⟨?_, ?_⟩
  · exact (Nat.lt_pow_self hp.one_lt).le
  · calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ p ^ 1 := Nat.pow_le_pow_left hp2 1
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf

/-- For every exceptional group of Lie type `S`, `|Out(S)| ≤ |S|`. -/
theorem card_outerAut_le_card_of_exceptionalSocle {S : Type} [Group S]
    (h : ExceptionalSocle S) : Nat.card (OuterAut S) ≤ Nat.card S := by
  rcases h with ⟨t, p, f, ht, hmodel⟩ | ⟨t, p, f, ht, hmodel⟩ | ⟨p, f, hmodel⟩
  · obtain ⟨hp, hf, -⟩ := hmodel.1
    obtain ⟨hfq, hq2⟩ := exp_le_prime_pow hp hf
    have hcard := card_chevalleyExceptionalModel hmodel
    cases t with
    | G2 =>
      rw [hcard]
      exact (card_outerAut_G2 hmodel).2.trans
        ((Nat.mul_le_mul (by decide : 2 ≤ 6) hfq).trans (six_mul_le_ordG2 hq2))
    | F4 =>
      rw [hcard]
      exact (card_outerAut_F4 hmodel).2.trans
        ((Nat.mul_le_mul (by decide : 2 ≤ 6) hfq).trans (six_mul_le_ordF4 hq2))
    | E6 =>
      rw [hcard]
      exact (card_outerAut_E6 hmodel).2.trans
        ((Nat.mul_le_mul_left 6 hfq).trans (six_mul_le_ordE6 hq2))
    | E7 =>
      rw [hcard]
      exact (card_outerAut_E7 hmodel).2.trans
        ((Nat.mul_le_mul (by decide : 2 ≤ 6) hfq).trans (six_mul_le_ordE7 hq2))
    | E8 =>
      rw [hcard]
      exact (card_outerAut_E8 hmodel).2.trans
        (hfq.trans ((Nat.le_mul_of_pos_left _ (by decide : 0 < 6)).trans (six_mul_le_ordE8 hq2)))
    | twistedE6 =>
      rw [hcard]
      exact (card_outerAut_twistedE6 hmodel).2.trans
        ((Nat.mul_le_mul_left 6 hfq).trans (six_mul_le_ordTwistedE6 hq2))
    | trialityD4 =>
      rw [hcard, card_outerAut_trialityD4 hmodel]
      exact (Nat.mul_le_mul (by decide : 3 ≤ 6) hfq).trans (six_mul_le_ordTrialityD4 hq2)
    | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus
    | twistedB2 | twistedG2 | twistedF4 | Tits => exact absurd ht (by decide)
  · cases t with
    | twistedG2 =>
      obtain ⟨rfl, ⟨a, ha, hfa⟩, hcard⟩ := card_reeTitsModel_twistedG2 hmodel
      obtain ⟨hfq, hq2⟩ := exp_le_prime_pow Nat.prime_three (by omega : 1 ≤ f)
      rw [hcard, card_outerAut_twistedG2 hmodel]
      exact hfq.trans (self_le_ordRee hq2)
    | twistedF4 =>
      obtain ⟨rfl, ⟨a, ha, hfa⟩, hcard⟩ := card_reeTitsModel_twistedF4 hmodel
      obtain ⟨hfq, hq2⟩ := exp_le_prime_pow Nat.prime_two (by omega : 1 ≤ f)
      rw [hcard, card_outerAut_twistedF4 hmodel]
      exact hfq.trans (self_le_ordTwistedF4 hq2)
    | Tits =>
      obtain ⟨hcard, hout⟩ := card_reeTitsModel_Tits hmodel
      rw [hcard, hout]
      decide
    | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus
    | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 => exact absurd ht (by decide)
  · obtain ⟨rfl, ⟨a, ha, hfa⟩, hcard⟩ := card_suzukiModel hmodel
    obtain ⟨hfq, hq2⟩ := exp_le_prime_pow Nat.prime_two (by omega : 1 ≤ f)
    rw [hcard]
    exact (card_outerAut_suzuki hmodel).2.trans (hfq.trans (self_le_ordSuzuki hq2))

/-- Every finite exceptional simple group of Lie type `S` satisfies `|Aut(S)| ≤ |S|²`. -/
theorem autBound_exceptional : AutBound ExceptionalSocle := by
  intro S _ _ hS
  rw [sq]
  exact (card_mulAut_le_card_mul_outerAut S).trans
    (Nat.mul_le_mul_left (Nat.card S) (card_outerAut_le_card_of_exceptionalSocle hS))

end Maroti
