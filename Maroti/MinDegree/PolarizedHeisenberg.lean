module

public import Mathlib.Algebra.CharP.Basic
public import Maroti.MinDegree.Heisenberg

/-!
# Minimum degree of faithful actions from polarized Heisenberg subgroups

Suppose a group `G` contains two abelian subgroups parameterized by `X, Y : V → G` and a central
subgroup parameterized by `z : K → G` (where `K` is a finite field of characteristic `p` and `V` is
a finite additive group of exponent `p`, such as `ι → K`), satisfying four conditions:
* The maps `X`, `Y`, and `z` are additive (`X (u₁ + u₂) = X u₁ * X u₂`,
  `Y (v₁ + v₂) = Y v₁ * Y v₂`, and `z (s₁ + s₂) = z s₁ * z s₂`).
* The map `z` is injective (`z s = 1 → s = 0`).
* Every `z s` commutes with `X u` and `Y v`.
* The commutator is `⁅X u, Y v⁆ = z (B u v)` for a bi-additive pairing `B : V → V → K` that is
  left- and right-surjective on nonzero arguments (`u ≠ 0 → Surjective (B u)` and
  `v ≠ 0 → Surjective (B · v)`).

Then the set `{ X u * Y v * z s | u, v : V, s : K }` is a subgroup `Q ≤ G` of order
`Nat.card V ^ 2 * Nat.card K` whose center contains `Z = { z s | s : K }` of order `Nat.card K` and
index `Nat.card V ^ 2`, and `(Q, Z)` satisfies all hypotheses of `Maroti.MinDegree.Heisenberg`.

Consequently, two bounds hold:
* Every faithful action of `G` on a finite type `α` satisfies `p * Nat.card V ≤ Nat.card α`.
* If `G` is a finite simple group, every proper subgroup `H ≠ ⊤` of `G` satisfies
  `p * Nat.card V ≤ H.index`.
-/

@[expose] public section

namespace Maroti

open Subgroup
open scoped commutatorElement

variable {K V G : Type*} [Field K] [AddCommGroup V] [Group G]

/-- Hypotheses for a polarized Heisenberg configuration `(X, Y, z, B)` in a group `G`. -/
structure PolarizedHeisenbergData (X Y : V → G) (z : K → G) (B : V → V → K) : Prop where
  X_add : ∀ u₁ u₂, X (u₁ + u₂) = X u₁ * X u₂
  Y_add : ∀ v₁ v₂, Y (v₁ + v₂) = Y v₁ * Y v₂
  z_add : ∀ s₁ s₂, z (s₁ + s₂) = z s₁ * z s₂
  z_eq_one : ∀ s, z s = 1 → s = 0
  commute_X_z : ∀ u s, Commute (X u) (z s)
  commute_Y_z : ∀ v s, Commute (Y v) (z s)
  comm_X_Y : ∀ u v, ⁅X u, Y v⁆ = z (B u v)
  B_add_left : ∀ u₁ u₂ v, B (u₁ + u₂) v = B u₁ v + B u₂ v
  B_add_right : ∀ u v₁ v₂, B u (v₁ + v₂) = B u v₁ + B u v₂
  B_surj_left : ∀ u, u ≠ 0 → ∀ s, ∃ v, B u v = s
  B_surj_right : ∀ v, v ≠ 0 → ∀ s, ∃ u, B u v = s

namespace PolarizedHeisenbergData

variable {X Y : V → G} {z : K → G} {B : V → V → K} (D : PolarizedHeisenbergData X Y z B)
include D

theorem X_zero : X 0 = 1 := by
  have h := D.X_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem Y_zero : Y 0 = 1 := by
  have h := D.Y_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem z_zero : z 0 = 1 := by
  have h := D.z_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem X_neg (u : V) : (X u)⁻¹ = X (-u) := by
  have h := D.X_add u (-u)
  rw [add_neg_cancel, D.X_zero] at h
  exact inv_eq_of_mul_eq_one_right h.symm

theorem Y_neg (v : V) : (Y v)⁻¹ = Y (-v) := by
  have h := D.Y_add v (-v)
  rw [add_neg_cancel, D.Y_zero] at h
  exact inv_eq_of_mul_eq_one_right h.symm

theorem z_neg (s : K) : (z s)⁻¹ = z (-s) := by
  have h := D.z_add s (-s)
  rw [add_neg_cancel, D.z_zero] at h
  exact inv_eq_of_mul_eq_one_right h.symm

theorem commute_X_X (u₁ u₂ : V) : Commute (X u₁) (X u₂) := by
  change X u₁ * X u₂ = X u₂ * X u₁
  rw [← D.X_add, ← D.X_add, add_comm]

theorem commute_Y_Y (v₁ v₂ : V) : Commute (Y v₁) (Y v₂) := by
  change Y v₁ * Y v₂ = Y v₂ * Y v₁
  rw [← D.Y_add, ← D.Y_add, add_comm]

theorem commute_z_z (s₁ s₂ : K) : Commute (z s₁) (z s₂) := by
  change z s₁ * z s₂ = z s₂ * z s₁
  rw [← D.z_add, ← D.z_add, add_comm]

theorem B_zero_left (v : V) : B 0 v = 0 := by
  have h := D.B_add_left 0 0 v
  rw [add_zero] at h
  exact add_eq_left.mp h.symm

theorem B_zero_right (u : V) : B u 0 = 0 := by
  have h := D.B_add_right u 0 0
  rw [add_zero] at h
  exact add_eq_left.mp h.symm

theorem B_neg_left (u v : V) : B (-u) v = -B u v := by
  have h := D.B_add_left u (-u) v
  rw [add_neg_cancel, D.B_zero_left] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem B_neg_right (u v : V) : B u (-v) = -B u v := by
  have h := D.B_add_right u v (-v)
  rw [add_neg_cancel, D.B_zero_right] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Reordering rule `Y v * X u = X u * Y v * z (-B u v)`. -/
theorem Y_mul_X (v u : V) : Y v * X u = X u * Y v * z (-B u v) := by
  have h1 := D.comm_X_Y u v
  rw [commutatorElement_def] at h1
  have h2 : X u * Y v = z (B u v) * Y v * X u := by
    calc X u * Y v = (X u * Y v * (X u)⁻¹ * (Y v)⁻¹) * Y v * X u := by group
      _ = z (B u v) * Y v * X u := by rw [h1]
  have hc : z (B u v) * (Y v * X u) = (Y v * X u) * z (B u v) :=
    ((D.commute_Y_z v (B u v)).symm.mul_right (D.commute_X_z u (B u v)).symm)
  calc Y v * X u
      = (Y v * X u) * (z (B u v) * z (-B u v)) := by
        rw [← D.z_add, add_neg_cancel, D.z_zero, mul_one]
    _ = ((Y v * X u) * z (B u v)) * z (-B u v) := by group
    _ = (z (B u v) * Y v * X u) * z (-B u v) := by rw [← hc]; group
    _ = X u * Y v * z (-B u v) := by rw [← h2]

/-- Multiplication law for normal-form elements `X u * Y v * z s`. -/
theorem mul_normalForm (u₁ v₁ u₂ v₂ : V) (s₁ s₂ : K) :
    (X u₁ * Y v₁ * z s₁) * (X u₂ * Y v₂ * z s₂) =
      X (u₁ + u₂) * Y (v₁ + v₂) * z (s₁ + s₂ - B u₂ v₁) := by
  have hc1 : z s₁ * (X u₂ * Y v₂) = (X u₂ * Y v₂) * z s₁ :=
    (D.commute_X_z u₂ s₁).symm.mul_right (D.commute_Y_z v₂ s₁).symm
  have hc2 : z (-B u₂ v₁) * Y v₂ = Y v₂ * z (-B u₂ v₁) := (D.commute_Y_z v₂ _).symm
  calc (X u₁ * Y v₁ * z s₁) * (X u₂ * Y v₂ * z s₂)
      = X u₁ * Y v₁ * (z s₁ * (X u₂ * Y v₂)) * z s₂ := by group
    _ = X u₁ * (Y v₁ * X u₂) * Y v₂ * (z s₁ * z s₂) := by rw [hc1]; group
    _ = X u₁ * (X u₂ * Y v₁ * z (-B u₂ v₁)) * Y v₂ * (z s₁ * z s₂) := by rw [D.Y_mul_X]
    _ = (X u₁ * X u₂) * (Y v₁ * (z (-B u₂ v₁) * Y v₂)) * (z s₁ * z s₂) := by group
    _ = (X u₁ * X u₂) * (Y v₁ * Y v₂) * (z (-B u₂ v₁) * (z s₁ * z s₂)) := by rw [hc2]; group
    _ = X (u₁ + u₂) * Y (v₁ + v₂) * z (s₁ + s₂ - B u₂ v₁) := by
        rw [← D.X_add, ← D.Y_add, ← D.z_add, ← D.z_add]
        congr 2
        ring

/-- Inverse law for normal-form elements `X u * Y v * z s`. -/
theorem inv_normalForm (u v : V) (s : K) :
    (X u * Y v * z s)⁻¹ = X (-u) * Y (-v) * z (-s - B u v) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [D.mul_normalForm, add_neg_cancel, add_neg_cancel, D.B_neg_left, D.X_zero, D.Y_zero,
    one_mul, one_mul]
  have h : s + (-s - B u v) - -B u v = 0 := by ring
  rw [h, D.z_zero]

/-- Uniqueness of the normal form `X u * Y v * z s`. -/
theorem normalForm_injective :
    Function.Injective (fun t : V × V × K => X t.1 * Y t.2.1 * z t.2.2) := by
  have heq_zero : ∀ u v s, X u * Y v * z s = 1 → u = 0 ∧ v = 0 ∧ s = 0 := by
    intro u v s h1
    have hu : u = 0 := by
      by_contra hu0
      obtain ⟨v', hv'⟩ := D.B_surj_left u hu0 1
      have hcY : Commute (Y v * z s) (Y v') :=
        (D.commute_Y_Y v v').mul_left (D.commute_Y_z v' s).symm
      have hcomm1 : ⁅X u * Y v * z s, Y v'⁆ = ⁅X u, Y v'⁆ := by
        simp only [commutatorElement_def]
        calc X u * Y v * z s * Y v' * (X u * Y v * z s)⁻¹ * (Y v')⁻¹
            = X u * ((Y v * z s) * Y v') * (Y v * z s)⁻¹ * (X u)⁻¹ * (Y v')⁻¹ := by group
          _ = X u * (Y v' * (Y v * z s)) * (Y v * z s)⁻¹ * (X u)⁻¹ * (Y v')⁻¹ := by rw [hcY.eq]
          _ = X u * Y v' * (X u)⁻¹ * (Y v')⁻¹ := by group
      rw [h1, commutatorElement_one_left, D.comm_X_Y, hv'] at hcomm1
      exact one_ne_zero (D.z_eq_one 1 hcomm1.symm)
    subst hu
    rw [D.X_zero, one_mul] at h1
    have hv : v = 0 := by
      by_contra hv0
      obtain ⟨u', hu'⟩ := D.B_surj_right v hv0 1
      have hcz : Commute (X u') (z s) := D.commute_X_z u' s
      have hcomm2 : ⁅X u', Y v * z s⁆ = ⁅X u', Y v⁆ := by
        simp only [commutatorElement_def]
        calc X u' * (Y v * z s) * (X u')⁻¹ * (Y v * z s)⁻¹
            = X u' * Y v * (z s * (X u')⁻¹) * (z s)⁻¹ * (Y v)⁻¹ := by group
          _ = X u' * Y v * ((X u')⁻¹ * z s) * (z s)⁻¹ * (Y v)⁻¹ := by rw [hcz.inv_left.symm.eq]
          _ = X u' * Y v * (X u')⁻¹ * (Y v)⁻¹ := by group
      rw [h1, commutatorElement_one_right, D.comm_X_Y, hu'] at hcomm2
      exact one_ne_zero (D.z_eq_one 1 hcomm2.symm)
    subst hv
    rw [D.Y_zero, one_mul] at h1
    exact ⟨rfl, rfl, D.z_eq_one s h1⟩
  rintro ⟨u₁, v₁, s₁⟩ ⟨u₂, v₂, s₂⟩ h
  have hmul : (X u₁ * Y v₁ * z s₁) * (X u₂ * Y v₂ * z s₂)⁻¹ = 1 := mul_inv_eq_one.mpr h
  rw [D.inv_normalForm, D.mul_normalForm] at hmul
  obtain ⟨hu, hv, hs⟩ := heq_zero _ _ _ hmul
  have hu' : u₁ = u₂ := add_neg_eq_zero.mp hu
  have hv' : v₁ = v₂ := add_neg_eq_zero.mp hv
  subst hu' hv'
  rw [D.B_neg_left] at hs
  have hs0 : s₁ + -s₂ = s₁ + (-s₂ - B u₁ v₁) - -B u₁ v₁ := by ring
  have hs' : s₁ = s₂ := add_neg_eq_zero.mp (hs0.trans hs)
  subst hs'
  rfl

/-- The Heisenberg subgroup `Q ≤ G` consisting of all `X u * Y v * z s`. -/
def heisSubgroup : Subgroup G where
  carrier := { g : G | ∃ u v s, X u * Y v * z s = g }
  one_mem' := ⟨0, 0, 0, by rw [D.X_zero, D.Y_zero, D.z_zero, mul_one, mul_one]⟩
  mul_mem' := by
    rintro _ _ ⟨u₁, v₁, s₁, rfl⟩ ⟨u₂, v₂, s₂, rfl⟩
    exact ⟨u₁ + u₂, v₁ + v₂, s₁ + s₂ - B u₂ v₁, (D.mul_normalForm u₁ v₁ u₂ v₂ s₁ s₂).symm⟩
  inv_mem' := by
    rintro _ ⟨u, v, s, rfl⟩
    exact ⟨-u, -v, -s - B u v, (D.inv_normalForm u v s).symm⟩

/-- Equivalence `(V × V) × K ≃ D.heisSubgroup` given by `(u, v, s) ↦ X u * Y v * z s`. -/
noncomputable def heisEquiv : V × V × K ≃ D.heisSubgroup :=
  Equiv.ofBijective
    (fun t => ⟨X t.1 * Y t.2.1 * z t.2.2, t.1, t.2.1, t.2.2, rfl⟩)
    ⟨fun _ _ h => D.normalForm_injective (congrArg Subtype.val h),
      fun ⟨_, u, v, s, hg⟩ => ⟨(u, v, s), Subtype.ext hg⟩⟩

/-- The central subgroup `Z ≤ D.heisSubgroup` consisting of all `z s`. -/
def centerSubgroup : Subgroup D.heisSubgroup where
  carrier := { q : D.heisSubgroup | ∃ s : K, X 0 * Y 0 * z s = q.1 }
  one_mem' := ⟨0, by rw [D.X_zero, D.Y_zero, D.z_zero, mul_one, mul_one]; rfl⟩
  mul_mem' := by
    rintro ⟨_, _, _, _, rfl⟩ ⟨_, _, _, _, rfl⟩ ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩
    refine ⟨s₁ + s₂, ?_⟩
    change X 0 * Y 0 * z (s₁ + s₂) = _ * _
    rw [← hs₁, ← hs₂, D.mul_normalForm, add_zero, D.B_zero_left, sub_zero]
  inv_mem' := by
    rintro ⟨_, _, _, _, rfl⟩ ⟨s, hs⟩
    refine ⟨-s, ?_⟩
    change X 0 * Y 0 * z (-s) = (_)⁻¹
    rw [← hs, D.inv_normalForm, neg_zero, D.B_zero_left, sub_zero]

/-- Equivalence `K ≃ D.centerSubgroup` given by `s ↦ z s`. -/
noncomputable def centerEquiv : K ≃ D.centerSubgroup :=
  Equiv.ofBijective
    (fun s => ⟨⟨X 0 * Y 0 * z s, 0, 0, s, rfl⟩, s, rfl⟩)
    ⟨fun s₁ s₂ h => by
      have h' := D.normalForm_injective (a₁ := (0, 0, s₁)) (a₂ := (0, 0, s₂))
        (congrArg (fun x : D.centerSubgroup => (x.1 : G)) h)
      exact congrArg (fun t : V × V × K => t.2.2) h',
      fun ⟨⟨_, _⟩, s, hs⟩ => ⟨s, Subtype.ext (Subtype.ext hs)⟩⟩

theorem mem_centerSubgroup_iff (u v : V) (s : K) :
    (⟨X u * Y v * z s, u, v, s, rfl⟩ : D.heisSubgroup) ∈ D.centerSubgroup ↔ u = 0 ∧ v = 0 := by
  constructor
  · rintro ⟨s', hs'⟩
    have h := D.normalForm_injective (a₁ := (0, 0, s')) (a₂ := (u, v, s)) hs'
    exact ⟨(congrArg Prod.fst h).symm, (congrArg (fun t : V × V × K => t.2.1) h).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨s, rfl⟩

/-- Commutator of two normal-form elements in `D.heisSubgroup`. -/
theorem comm_normalForm (u₁ v₁ u₂ v₂ : V) (s₁ s₂ : K) :
    ⁅X u₁ * Y v₁ * z s₁, X u₂ * Y v₂ * z s₂⁆ = X 0 * Y 0 * z (B u₁ v₂ - B u₂ v₁) := by
  rw [commutatorElement_def, D.mul_normalForm, D.inv_normalForm, D.inv_normalForm,
    D.mul_normalForm, D.mul_normalForm]
  have hu : u₁ + u₂ + -u₁ + -u₂ = 0 := by abel
  have hv : v₁ + v₂ + -v₁ + -v₂ = 0 := by abel
  have hv1 : v₁ + v₂ + -v₁ = v₂ := by abel
  rw [hu, hv, hv1, D.B_neg_left, D.B_neg_left, D.B_add_right]
  congr 2
  ring

theorem centerSubgroup_le_center : D.centerSubgroup ≤ center D.heisSubgroup := by
  rintro ⟨_, u, v, s, rfl⟩ hs
  rw [D.mem_centerSubgroup_iff] at hs
  obtain ⟨rfl, rfl⟩ := hs
  rw [mem_center_iff]
  rintro ⟨_, u', v', s', rfl⟩
  apply Subtype.ext
  change (X u' * Y v' * z s') * (X 0 * Y 0 * z s) = (X 0 * Y 0 * z s) * (X u' * Y v' * z s')
  rw [D.mul_normalForm, D.mul_normalForm, add_zero, zero_add, add_zero, zero_add,
    D.B_zero_left, D.B_zero_right, sub_zero, sub_zero, add_comm s' s]

theorem commutator_mem_centerSubgroup (q₁ q₂ : D.heisSubgroup) :
    ⁅q₁, q₂⁆ ∈ D.centerSubgroup := by
  rcases q₁ with ⟨_, u₁, v₁, s₁, rfl⟩
  rcases q₂ with ⟨_, u₂, v₂, s₂, rfl⟩
  refine ⟨B u₁ v₂ - B u₂ v₁, ?_⟩
  exact (D.comm_normalForm u₁ v₁ u₂ v₂ s₁ s₂).symm

theorem exists_commutator_eq_of_not_mem {q₁ : D.heisSubgroup} (hq₁ : q₁ ∉ D.centerSubgroup)
    {z₀ : D.heisSubgroup} (hz₀ : z₀ ∈ D.centerSubgroup) :
    ∃ q₂ : D.heisSubgroup, ⁅q₁, q₂⁆ = z₀ := by
  rcases q₁ with ⟨_, u₁, v₁, s₁, rfl⟩
  obtain ⟨t, ht⟩ := hz₀
  rw [D.mem_centerSubgroup_iff, not_and_or] at hq₁
  rcases hq₁ with hu₁ | hv₁
  · obtain ⟨v₂, hv₂⟩ := D.B_surj_left u₁ hu₁ t
    refine ⟨⟨X 0 * Y v₂ * z 0, 0, v₂, 0, rfl⟩, Subtype.ext ?_⟩
    change ⁅X u₁ * Y v₁ * z s₁, X 0 * Y v₂ * z 0⁆ = z₀.1
    rw [D.comm_normalForm, D.B_zero_left, sub_zero, hv₂, ht]
  · obtain ⟨u₂, hu₂⟩ := D.B_surj_right v₁ hv₁ (-t)
    refine ⟨⟨X u₂ * Y 0 * z 0, u₂, 0, 0, rfl⟩, Subtype.ext ?_⟩
    change ⁅X u₁ * Y v₁ * z s₁, X u₂ * Y 0 * z 0⁆ = z₀.1
    rw [D.comm_normalForm, D.B_zero_right, zero_sub, hu₂, neg_neg, ht]

theorem index_centerSubgroup [Finite K] [Finite V] :
    D.centerSubgroup.index = Nat.card V ^ 2 := by
  have : Finite D.heisSubgroup := Finite.of_equiv _ D.heisEquiv
  have hmul := Subgroup.index_mul_card D.centerSubgroup
  have hQ : Nat.card D.heisSubgroup = Nat.card V ^ 2 * Nat.card K := by
    rw [← Nat.card_congr D.heisEquiv, Nat.card_prod, Nat.card_prod, sq, mul_assoc]
  have hZ : Nat.card D.centerSubgroup = Nat.card K :=
    (Nat.card_congr D.centerEquiv).symm
  rw [hQ, hZ] at hmul
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul

theorem centerSubgroup_ne_bot [Finite K] : D.centerSubgroup ≠ ⊥ := by
  intro hbot
  have hZ : Nat.card D.centerSubgroup = Nat.card K :=
    (Nat.card_congr D.centerEquiv).symm
  rw [hbot, Subgroup.card_bot] at hZ
  exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne hZ

theorem pow_p_mem_centerSubgroup {p : ℕ} [CharP K p] (hV : ∀ u : V, p • u = 0)
    (q : D.heisSubgroup) :
    q ^ p ∈ D.centerSubgroup := by
  have hZnorm : D.centerSubgroup.Normal :=
    normal_of_le_of_commutator_le D.commutator_mem_centerSubgroup D.centerSubgroup le_rfl
  let _ : CommGroup (D.heisSubgroup ⧸ D.centerSubgroup) :=
    { (inferInstance : Group (D.heisSubgroup ⧸ D.centerSubgroup)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with | H x =>
        induction b using QuotientGroup.induction_on with | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hxy : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def]; group
        rw [hxy]
        exact D.commutator_mem_centerSubgroup y⁻¹ x⁻¹ }
  have hXpow : ∀ (n : ℕ) (u : V), X (n • u) = X u ^ n := fun n u => by
    induction n with
    | zero => rw [zero_smul, pow_zero, D.X_zero]
    | succ n ih => rw [succ_nsmul, pow_succ, D.X_add, ih]
  have hYpow : ∀ (n : ℕ) (v : V), Y (n • v) = Y v ^ n := fun n v => by
    induction n with
    | zero => rw [zero_smul, pow_zero, D.Y_zero]
    | succ n ih => rw [succ_nsmul, pow_succ, D.Y_add, ih]
  have hzpow : ∀ (n : ℕ) (s : K), z (n • s) = z s ^ n := fun n s => by
    induction n with
    | zero => rw [zero_smul, pow_zero, D.z_zero]
    | succ n ih => rw [succ_nsmul, pow_succ, D.z_add, ih]
  rcases q with ⟨_, u, v, s, rfl⟩
  let qX : D.heisSubgroup := ⟨X u * Y 0 * z 0, u, 0, 0, rfl⟩
  let qY : D.heisSubgroup := ⟨X 0 * Y v * z 0, 0, v, 0, rfl⟩
  let qZ : D.heisSubgroup := ⟨X 0 * Y 0 * z s, 0, 0, s, rfl⟩
  have hprod : (⟨X u * Y v * z s, u, v, s, rfl⟩ : D.heisSubgroup) = qX * qY * qZ := by
    apply Subtype.ext
    change X u * Y v * z s = (X u * Y 0 * z 0) * (X 0 * Y v * z 0) * (X 0 * Y 0 * z s)
    rw [D.Y_zero, D.X_zero, D.z_zero]
    group
  rw [hprod, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, mul_pow, mul_pow, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow,
    ← QuotientGroup.mk_pow]
  have hqXp : qX ^ p = 1 := by
    apply Subtype.ext
    change (X u * Y 0 * z 0) ^ p = 1
    rw [D.Y_zero, D.z_zero, mul_one, mul_one, ← hXpow, hV u, D.X_zero]
  have hqYp : qY ^ p = 1 := by
    apply Subtype.ext
    change (X 0 * Y v * z 0) ^ p = 1
    rw [D.X_zero, D.z_zero, one_mul, mul_one, ← hYpow, hV v, D.Y_zero]
  have hqZp : qZ ^ p = 1 := by
    apply Subtype.ext
    change (X 0 * Y 0 * z s) ^ p = 1
    rw [D.X_zero, D.Y_zero, one_mul, one_mul, ← hzpow, nsmul_eq_mul, CharP.cast_eq_zero K p,
      zero_mul, D.z_zero]
  rw [hqXp, hqYp, hqZp, QuotientGroup.mk_one, mul_one, mul_one]

theorem pow_p_eq_one_of_mem_centerSubgroup {p : ℕ} [CharP K p] {q : D.heisSubgroup}
    (hq : q ∈ D.centerSubgroup) :
    q ^ p = 1 := by
  have hzpow : ∀ (n : ℕ) (s : K), z (n • s) = z s ^ n := fun n s => by
    induction n with
    | zero => rw [zero_smul, pow_zero, D.z_zero]
    | succ n ih => rw [succ_nsmul, pow_succ, D.z_add, ih]
  obtain ⟨s, hs⟩ := hq
  apply Subtype.ext
  change (q.1 : G) ^ p = 1
  rw [← hs, D.X_zero, D.Y_zero, one_mul, one_mul, ← hzpow, nsmul_eq_mul, CharP.cast_eq_zero K p,
    zero_mul, D.z_zero]

/-- If `G` acts faithfully on a finite type `α`, then `p * Nat.card V ≤ Nat.card α`. -/
theorem mul_card_le_card_of_faithfulSMul [Finite K] [Finite V] {p : ℕ} [Fact p.Prime]
    [CharP K p] (hV : ∀ u : V, p • u = 0)
    {α : Type*} [Finite α] [MulAction G α] [FaithfulSMul G α] :
    p * Nat.card V ≤ Nat.card α := by
  have : Finite D.heisSubgroup := Finite.of_equiv _ D.heisEquiv
  exact mul_le_card_of_injective_of_faithfulSMul
    D.centerSubgroup_le_center
    D.commutator_mem_centerSubgroup
    (fun _ hq => D.pow_p_eq_one_of_mem_centerSubgroup hq)
    (D.pow_p_mem_centerSubgroup hV)
    (fun _ hq _ hz => D.exists_commutator_eq_of_not_mem hq hz)
    D.heisSubgroup.subtype D.heisSubgroup.subtype_injective
    D.centerSubgroup_ne_bot D.index_centerSubgroup.symm.le

/-- If `G` is a finite simple group, every proper subgroup `H ≠ ⊤` of `G` has index
`p * Nat.card V ≤ H.index`. -/
theorem mul_card_le_index_of_ne_top [Finite K] [Finite V] {p : ℕ} [Fact p.Prime] [CharP K p]
    [Finite G] [IsSimpleGroup G] (hV : ∀ u : V, p • u = 0)
    {H : Subgroup G} (hH : H ≠ ⊤) :
    p * Nat.card V ≤ H.index := by
  have : FaithfulSMul G (G ⧸ H) := faithfulSMul_quotient_of_ne_top hH
  exact D.mul_card_le_card_of_faithfulSMul hV (α := G ⧸ H)

end PolarizedHeisenbergData

end Maroti
