module

public import Maroti.Statement
public import CFSG.Open.StatedDefs
public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.NativeSporadic

/-!
# The steps of the proof of Theorem 1.1

Maróti proves Theorem 1.1 in four steps (Section 2 of the paper).

1. Groups that are not almost simple (affine, diagonal, product and twisted wreath type) satisfy
   the theorem if almost simple groups do.
2. Almost simple groups whose socle is classical but not `PSL`, exceptional of Lie type, or
   sporadic satisfy case (ii) or (iii).
3. Almost simple groups with socle `A_m` satisfy case (i) with `r = 1`, or case (iii). Maróti
   treats `m ≥ 7` here and `A₅ ≅ PSL(2, 4)`, `A₆ ≅ PSL(2, 9)` in step 4. We treat all `m ≥ 5`
   here.
4. Almost simple groups with socle `PSL(t, q)` satisfy case (i) with `r = 1`, or case (iii)
   (Lemma 2.2).

This file states what each step proves. The classification of finite simple groups, in the form
`TauCeti.ClassificationStatement`, together with the models of AxiomMath/CFSG
(`CFSG.Blueprint.Catalog`), says that every socle falls under one of the families below.
-/

@[expose] public section

namespace Maroti

open Equiv

variable {α : Type*}

/-- Case (i) of Theorem 1.1 with `r = 1` and `m ≥ 5`: there are `m ≥ 5`, `k` and an
identification `e` of the points with the `k`-element subsets of `Fin m` such that, read through
`e`, every element of `G` is a permutation of `Fin m`, and `G` contains `A_m`. -/
def IsSubsetActionType (G : Subgroup (Perm α)) : Prop :=
  ∃ (m k : ℕ) (e : α ≃ KSubset m k), 5 ≤ m ∧
    (∀ g ∈ G, ∃ h : Perm (Fin m), e.permCongr g = kSubsetPerm h) ∧
    ∀ a : alternatingGroup (Fin m), e.symm.permCongr (kSubsetPerm (a : Perm (Fin m))) ∈ G

/-- Case (i) of Theorem 1.1 with `5 ≤ m`, before normalizing `k` and `r`: there are `m ≥ 5`, `k`,
`r` and an identification `e` of the points with the `r`-tuples of `k`-element subsets of `Fin m`
such that, read through `e`, every element of `G` is an element of `S_m wr S_r` in the product
action, and `G` contains `(A_m)^r` acting coordinatewise. -/
def IsWreathType (G : Subgroup (Perm α)) : Prop :=
  ∃ (m k r : ℕ) (e : α ≃ (Fin r → KSubset m k)), 5 ≤ m ∧
    (∀ g ∈ G, ∃ (σ : Perm (Fin r)) (h : Fin r → Perm (Fin m)),
      e.permCongr g = productActionPerm σ h) ∧
    ∀ a : Fin r → alternatingGroup (Fin m),
      e.symm.permCongr (productActionPerm 1 fun i => (a i : Perm (Fin m))) ∈ G

/-- The conclusion of Step 1 of Theorem 1.1, with `IsWreathType` in case (i) and without the last
inequality of case (iii). -/
def Conclusion (G : Subgroup (Perm α)) : Prop :=
  IsWreathType G ∨ IsMathieuType G ∨ Nat.card G ≤ bound (Nat.card α)

/-- The conclusion of Theorem 1.1 for almost simple groups: case (i) with `r = 1` and `m ≥ 5`,
case (ii), or the inequality of case (iii). -/
def AlmostSimpleConclusion (G : Subgroup (Perm α)) : Prop :=
  IsSubsetActionType G ∨ IsMathieuType G ∨ Nat.card G ≤ bound (Nat.card α)

/-- The group `G` is almost simple with socle isomorphic to `S`: a subgroup `T ≤ G` normalized
by `G` is a nonabelian simple group isomorphic to `S`, and only the identity of `G` commutes with
every element of `T`. -/
def IsAlmostSimpleWith (G : Subgroup (Perm α)) (S : Type*) [Group S] : Prop :=
  ∃ T : Subgroup (Perm α), T ≤ G ∧ (∀ g ∈ G, ∀ t ∈ T, g * t * g⁻¹ ∈ T) ∧
    IsSimpleGroup T ∧ (∃ a b : T, a * b ≠ b * a) ∧
    (∀ g ∈ G, (∀ t ∈ T, g * t = t * g) → g = 1) ∧ Nonempty (T ≃* S)

/-- Theorem 1.1 for the almost simple groups whose socle lies in the family `P`. -/
def AlmostSimpleCase (P : ∀ (S : Type) [Group S], Prop) : Prop :=
  ∀ (α : Type) [Finite α] (G : Subgroup (Perm α)) (S : Type) [Group S],
    MulAction.IsPreprimitive G α → IsAlmostSimpleWith G S → P S → AlmostSimpleConclusion G

/-- Every group in the family `P` has at most `|S|²` automorphisms. -/
def AutBound (P : ∀ (S : Type) [Group S], Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], P S → Nat.card (MulAut S) ≤ Nat.card S ^ 2

/-- The group `S` is a nonabelian simple group. -/
def IsNonabelianSimple (S : Type) [Group S] : Prop :=
  IsSimpleGroup S ∧ ∃ a b : S, a * b ≠ b * a

/-- Step 3: alternating groups of degree at least 5. -/
def AlternatingSocle (S : Type) [Group S] : Prop :=
  ∃ m, 5 ≤ m ∧ Nonempty (S ≃* alternatingGroup (Fin m))

/-- Step 4 (Lemma 2.2): projective special linear groups. -/
def LinearSocle (S : Type) [Group S] : Prop :=
  ∃ n p f, CFSG.Open.StatedClassicalModel S .PSL n p f

/-- Step 2: the classical groups other than `PSL`. -/
def OtherClassicalSocle (S : Type) [Group S] : Prop :=
  ∃ t n p f, t ≠ CFSG.Open.StatedLieTag.PSL ∧ CFSG.Open.StatedClassicalModel S t n p f

/-- The classical groups with one Lie tag `t`. The other classical groups are treated one tag at
a time. -/
def ClassicalSocle (t : CFSG.Open.StatedLieTag) (S : Type) [Group S] : Prop :=
  ∃ n p f, CFSG.Open.StatedClassicalModel S t n p f

/-- The symplectic groups `PSp(2n, q)` with `q` even. -/
def SymplecticSocleEven (S : Type) [Group S] : Prop :=
  ∃ n f, CFSG.Open.StatedClassicalModel S .PSp n 2 f

/-- The symplectic groups `PSp(2n, q)` with `q` odd. -/
def SymplecticSocleOdd (S : Type) [Group S] : Prop :=
  ∃ n p f, p ≠ 2 ∧ CFSG.Open.StatedClassicalModel S .PSp n p f

/-- Step 2: the exceptional groups of Lie type. -/
def ExceptionalSocle (S : Type) [Group S] : Prop :=
  CFSG.Blueprint.ExceptionalRep S

/-- Step 2: the sporadic groups. -/
def SporadicSocle (S : Type) [Group S] : Prop :=
  CFSG.Blueprint.NativeSporadic.SporadicRep S

end Maroti
