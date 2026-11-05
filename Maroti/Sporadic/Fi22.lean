module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
import Maroti.Sporadic.Fi23
import Maroti.Sporadic.ExtraspecialCoord
import Certificates.Kernel.SlpRelC.Fi22Glue
import CFSG.Sporadic.Fi22.Simple
import all CFSG.Blueprint.NativeSporadic

/-!
# Sporadic Simple Group `Fi₂₂`

This file proves Maróti's bound `Nat.card G ≤ bound (Nat.card α)` for primitive almost simple
groups `G` whose socle `S` is isomorphic to Fischer's group `Fi₂₂` (Maróti, *On the orders of
primitive groups*, J. Algebra 258 (2002), Theorem 1.1).

Using `Certificates.Kernel.SlpRelC.Fi22Glue`, `Fi₂₂` has an extraspecial Heisenberg `3`-subgroup
`Q` of order `3⁷ = 2187` (`HeisCfg 3 3`) together with two normalizing elements `dA` and `n` acting
irreducibly on `Q / Z(Q) ≅ (ZMod 3)⁶`. Every proper subgroup of `Fi₂₂` therefore has index at
least `2 * 3⁴ = 162 ≥ 114`.
-/

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Maroti

open Subgroup
open CFSG.Blueprint CFSG.Sporadic.Fi22
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open CFSG.HardMathSupport.Solomon.Coordinator.B3B
open CertificateChecks.KernelSlpRel
open scoped commutatorElement Matrix

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

set_option maxRecDepth 400000

private theorem fi22_extra_ok :
    fi22SlpK fi22CoverProg [([28, 47], [35, 28]), ([28, 46], [35, 45, 41, 41, 28])] [] = true := by
  decide +kernel

private theorem fi22_full_cover_of_rels {G : Type*} [Group G] (r : ℕ → G)
    (hr1 : ∀ p ∈ fi22CoverRels, (p.1.map r).prod = (p.2.map r).prod) (hz : r 41 ≠ 1)
    (hr2 : ∀ p ∈ ([([28, 47], [35, 28]), ([28, 46], [35, 45, 41, 41, 28])] :
      List (List ℕ × List ℕ)), (p.1.map r).prod = (p.2.map r).prod) :
    ∃ p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n : G,
      Fi22CoverData p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n ∧
      n * p₂ = p₀ * n ∧
      n * q₂ = p₀ * (q₀ * (z * (z * n))) := by
  have hcov := fi22_cover_of_rels r hr1 hz
  simp only [List.forall_mem_cons, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one] at hr2
  exact ⟨r 35, r 31, r 47, r 45, r 48, r 46, r 41, r 49, r 50, r 28,
    hcov, hr2.1, hr2.2.1⟩

private theorem fi22_full_cover :
    ∃ p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n : J,
      Fi22CoverData p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n ∧
      n * p₂ = p₀ * n ∧
      n * q₂ = p₀ * (q₀ * (z * (z * n))) := by
  have h1 := fi22Slp_rels fi22Hom_injective fi22Hom_a fi22Hom_b ch129041_ok
  have h2 := fi22Slp_rels fi22Hom_injective fi22Hom_a fi22Hom_b fi22_extra_ok
  exact fi22_full_cover_of_rels _ h1.1 (h1.2 41 List.mem_cons_self) h2.1

attribute [local irreducible] NativeSporadic.seedMonoid

section IrreducibleModule

private abbrev Fi22Vec := (Fin 3 → ZMod 3) × (Fin 3 → ZMod 3)

private def fi22E0 : Fin 3 → ZMod 3 := ![1, 0, 0]
private def fi22E1 : Fin 3 → ZMod 3 := ![0, 1, 0]
private def fi22E2 : Fin 3 → ZMod 3 := ![0, 0, 1]

private def bP0 : Fi22Vec := (fi22E0, 0)
private def bP1 : Fi22Vec := (fi22E1, 0)
private def bP2 : Fi22Vec := (fi22E2, 0)
private def bQ0 : Fi22Vec := (0, fi22E0)
private def bQ1 : Fi22Vec := (0, fi22E1)
private def bQ2 : Fi22Vec := (0, fi22E2)

private def fi22LinComb (p0 p1 p2 q0 q1 q2 : Fi22Vec) (w : Fi22Vec) : Fi22Vec :=
  w.1 0 • p0 + w.1 1 • p1 + w.1 2 • p2 + w.2 0 • q0 + w.2 1 • q1 + w.2 2 • q2

private def fi22ActDA : Fi22Vec → Fi22Vec :=
  fi22LinComb ((2 : ZMod 3) • bP0) bP1 ((2 : ZMod 3) • bP2)
    ((2 : ZMod 3) • bQ0) bQ1 ((2 : ZMod 3) • bQ2)

private def fi22ActN : Fi22Vec → Fi22Vec :=
  fi22LinComb ((2 : ZMod 3) • bP1) bQ2 bP0
    (bP1 + (2 : ZMod 3) • bQ1) ((2 : ZMod 3) • bP2) (bP0 + bQ0)

private theorem fi22Vec_decomp (w : Fi22Vec) :
    fi22LinComb bP0 bP1 bP2 bQ0 bQ1 bQ2 w = w := by
  rcases w with ⟨u, v⟩
  ext i <;> fin_cases i <;>
    simp [fi22LinComb, bP0, bP1, bP2, bQ0, bQ1, bQ2, fi22E0, fi22E1, fi22E2]

private theorem fi22Proj_coord : ∀ (a b c : ZMod 3) (i : Fin 3),
    2 * ((![a, b, c] : Fin 3 → ZMod 3) i +
      (a * (2 * fi22E0 i) + b * fi22E1 i + c * (2 * fi22E2 i))) = b * fi22E1 i := by
  decide

private theorem fi22Proj_eq (w : Fi22Vec) :
    (2 : ZMod 3) • (w + fi22ActDA w) = w.1 1 • bP1 + w.2 1 • bQ1 := by
  rcases w with ⟨u, v⟩
  ext i
  · have hu : u i = (![u 0, u 1, u 2] : Fin 3 → ZMod 3) i := by fin_cases i <;> rfl
    change 2 * (u i + (u 0 * (2 * fi22E0 i) + u 1 * fi22E1 i + u 2 * (2 * fi22E2 i) +
      v 0 * 0 + v 1 * 0 + v 2 * 0)) = u 1 * fi22E1 i + v 1 * 0
    rw [mul_zero, mul_zero, mul_zero, add_zero, add_zero, add_zero, add_zero, hu]
    exact fi22Proj_coord (u 0) (u 1) (u 2) i
  · have hv : v i = (![v 0, v 1, v 2] : Fin 3 → ZMod 3) i := by fin_cases i <;> rfl
    change 2 * (v i + (u 0 * 0 + u 1 * 0 + u 2 * 0 +
      v 0 * (2 * fi22E0 i) + v 1 * fi22E1 i + v 2 * (2 * fi22E2 i))) = u 1 * 0 + v 1 * fi22E1 i
    rw [mul_zero, mul_zero, mul_zero, add_zero, add_zero, zero_add, zero_add, hv]
    exact fi22Proj_coord (v 0) (v 1) (v 2) i

private theorem fi22ActN_cube_plane : ∀ a b : ZMod 3,
    fi22ActN (fi22ActN (fi22ActN (a • bP1 + b • bQ1))) = b • bP1 + (2 * a) • bQ1 := by
  decide

private theorem fi22_plane_span_bP1 : ∀ a b d : ZMod 3,
    (2 * d * a) • (a • bP1 + b • bQ1) + (-d * b) • (b • bP1 + (2 * a) • bQ1) =
      ((2 * a ^ 2 - b ^ 2) * d) • bP1 := by
  decide

private theorem fi22_plane_span_bQ1 : ∀ a b d : ZMod 3,
    (-d * b) • (a • bP1 + b • bQ1) + (d * a) • (b • bP1 + (2 * a) • bQ1) =
      ((2 * a ^ 2 - b ^ 2) * d) • bQ1 := by
  decide

private theorem fi22_det_sq :
    ∀ a b : ZMod 3, a ≠ 0 ∨ b ≠ 0 → (2 * a ^ 2 - b ^ 2) * (2 * a ^ 2 - b ^ 2) = 1 := by
  decide

private theorem fi22_actN_coord1_of_coord0 (w : Fi22Vec) (h0 : w.1 0 ≠ 0 ∨ w.2 0 ≠ 0) :
    (fi22ActN w).1 1 ≠ 0 ∨ (fi22ActN w).2 1 ≠ 0 := by
  have h1 : (fi22ActN w).1 1 = w.1 0 * 2 + w.2 0 := by
    simp [fi22ActN, fi22LinComb, bP0, bP1, bP2, bQ0, bQ1, bQ2, fi22E0, fi22E1, fi22E2]
  have h2 : (fi22ActN w).2 1 = w.2 0 * 2 := by
    simp [fi22ActN, fi22LinComb, bP0, bP1, bP2, bQ0, bQ1, bQ2, fi22E0, fi22E1, fi22E2]
  rw [h1, h2]
  have hdec : ∀ x y : ZMod 3, x ≠ 0 ∨ y ≠ 0 → x * 2 + y ≠ 0 ∨ y * 2 ≠ 0 := by decide
  exact hdec (w.1 0) (w.2 0) h0

private theorem fi22_actN2_coord1_of_coord2 (w : Fi22Vec) (h2 : w.1 2 ≠ 0 ∨ w.2 2 ≠ 0) :
    (fi22ActN (fi22ActN w)).1 1 ≠ 0 ∨ (fi22ActN (fi22ActN w)).2 1 ≠ 0 := by
  have h1 : (fi22ActN (fi22ActN w)).1 1 = (w.1 2 + w.2 2) * 2 + w.2 2 := by
    simp [fi22ActN, fi22LinComb, bP0, bP1, bP2, bQ0, bQ1, bQ2, fi22E0, fi22E1, fi22E2]
  have h2' : (fi22ActN (fi22ActN w)).2 1 = w.2 2 * 2 := by
    simp [fi22ActN, fi22LinComb, bP0, bP1, bP2, bQ0, bQ1, bQ2, fi22E0, fi22E1, fi22E2]
  rw [h1, h2']
  have hdec : ∀ x y : ZMod 3, x ≠ 0 ∨ y ≠ 0 → (x + y) * 2 + y ≠ 0 ∨ y * 2 ≠ 0 := by decide
  exact hdec (w.1 2) (w.2 2) h2

private theorem fi22_basis_from_bP1_bQ1 :
    fi22ActN bP1 = bQ2 ∧
    (2 : ZMod 3) • fi22ActN bQ1 = bP2 ∧
    fi22ActN bP2 = bP0 ∧
    fi22ActN bQ2 - bP0 = bQ0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (ext i <;> fin_cases i <;> decide)

private theorem fi22_mem_of_invariant {U : AddSubgroup Fi22Vec}
    (hDA : ∀ w ∈ U, fi22ActDA w ∈ U) (hN : ∀ w ∈ U, fi22ActN w ∈ U)
    {w₀ : Fi22Vec} (hw₀U : w₀ ∈ U) (hw₀ : w₀ ≠ 0) (y : Fi22Vec) :
    y ∈ U := by
  have hsmul : ∀ (c : ZMod 3) {w : Fi22Vec}, w ∈ U → c • w ∈ U := by
    intro c w hw
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
    exact U.nsmul_mem hw c.val
  have hproj : ∀ {w : Fi22Vec}, w ∈ U → w.1 1 • bP1 + w.2 1 • bQ1 ∈ U := by
    intro w hw
    rw [← fi22Proj_eq w]
    exact hsmul 2 (U.add_mem hw (hDA w hw))
  have hex_plane : ∃ a b : ZMod 3, (a ≠ 0 ∨ b ≠ 0) ∧ a • bP1 + b • bQ1 ∈ U := by
    by_cases h1 : w₀.1 1 ≠ 0 ∨ w₀.2 1 ≠ 0
    · exact ⟨w₀.1 1, w₀.2 1, h1, hproj hw₀U⟩
    · by_cases h0 : w₀.1 0 ≠ 0 ∨ w₀.2 0 ≠ 0
      · exact ⟨(fi22ActN w₀).1 1, (fi22ActN w₀).2 1,
          fi22_actN_coord1_of_coord0 w₀ h0, hproj (hN w₀ hw₀U)⟩
      · have h2 : w₀.1 2 ≠ 0 ∨ w₀.2 2 ≠ 0 := by
          push Not at h1 h0
          by_contra! h2
          apply hw₀
          rw [← fi22Vec_decomp w₀]
          unfold fi22LinComb
          rw [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]
          simp
        exact ⟨(fi22ActN (fi22ActN w₀)).1 1, (fi22ActN (fi22ActN w₀)).2 1,
          fi22_actN2_coord1_of_coord2 w₀ h2, hproj (hN _ (hN w₀ hw₀U))⟩
  obtain ⟨a, b, hab, habU⟩ := hex_plane
  have habU' : b • bP1 + (2 * a) • bQ1 ∈ U := by
    rw [← fi22ActN_cube_plane a b]
    exact hN _ (hN _ (hN _ habU))
  set d : ZMod 3 := 2 * a ^ 2 - b ^ 2
  have hd : (2 * a ^ 2 - b ^ 2) * d = 1 := fi22_det_sq a b hab
  have hbP1 : bP1 ∈ U := by
    have h := U.add_mem (hsmul (2 * d * a) habU) (hsmul (-d * b) habU')
    rwa [fi22_plane_span_bP1, hd, one_smul] at h
  have hbQ1 : bQ1 ∈ U := by
    have h := U.add_mem (hsmul (-d * b) habU) (hsmul (d * a) habU')
    rwa [fi22_plane_span_bQ1, hd, one_smul] at h
  obtain ⟨hQ2, hP2, hP0, hQ0⟩ := fi22_basis_from_bP1_bQ1
  have hbQ2 : bQ2 ∈ U := hQ2 ▸ hN bP1 hbP1
  have hbP2 : bP2 ∈ U := hP2 ▸ hsmul 2 (hN bQ1 hbQ1)
  have hbP0 : bP0 ∈ U := hP0 ▸ hN bP2 hbP2
  have hbQ0 : bQ0 ∈ U := hQ0 ▸ U.sub_mem (hN bQ2 hbQ2) hbP0
  rw [← fi22Vec_decomp y]
  exact U.add_mem (U.add_mem (U.add_mem (U.add_mem (U.add_mem
    (hsmul (y.1 0) hbP0) (hsmul (y.1 1) hbP1)) (hsmul (y.1 2) hbP2))
    (hsmul (y.2 0) hbQ0)) (hsmul (y.2 1) hbQ1)) (hsmul (y.2 2) hbQ2)

end IrreducibleModule

section GroupAction

private noncomputable def heisCoordVec {G : Type*} [Group G]
    {fX fY : (Fin 3 → ZMod 3) → G} {fz : ZMod 3 → G}
    {fB : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3) → ZMod 3}
    (D : PolarizedHeisenbergData fX fY fz fB) (q : D.heisSubgroup) : Fi22Vec :=
  ((D.heisEquiv.symm q).1, (D.heisEquiv.symm q).2.1)

private theorem heisCoordVec_mk {G : Type*} [Group G]
    {fX fY : (Fin 3 → ZMod 3) → G} {fz : ZMod 3 → G}
    {fB : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3) → ZMod 3}
    (D : PolarizedHeisenbergData fX fY fz fB) (u v : Fin 3 → ZMod 3) (s : ZMod 3) :
    heisCoordVec D ⟨fX u * fY v * fz s, u, v, s, rfl⟩ = (u, v) := by
  have h : (⟨fX u * fY v * fz s, u, v, s, rfl⟩ : D.heisSubgroup) = D.heisEquiv (u, v, s) := rfl
  rw [heisCoordVec, h, D.heisEquiv.symm_apply_apply]

private theorem heisCoordVec_one {G : Type*} [Group G]
    {fX fY : (Fin 3 → ZMod 3) → G} {fz : ZMod 3 → G}
    {fB : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3) → ZMod 3}
    (D : PolarizedHeisenbergData fX fY fz fB) :
    heisCoordVec D 1 = 0 := by
  have h1 : (1 : D.heisSubgroup) = ⟨fX 0 * fY 0 * fz 0, 0, 0, 0, rfl⟩ := by
    apply Subtype.ext
    change (1 : G) = fX 0 * fY 0 * fz 0
    rw [D.X_zero, D.Y_zero, D.z_zero, mul_one, mul_one]
  rw [h1, heisCoordVec_mk]
  rfl

private theorem heisCoordVec_mul {G : Type*} [Group G]
    {fX fY : (Fin 3 → ZMod 3) → G} {fz : ZMod 3 → G}
    {fB : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3) → ZMod 3}
    (D : PolarizedHeisenbergData fX fY fz fB) (q₁ q₂ : D.heisSubgroup) :
    heisCoordVec D (q₁ * q₂) = heisCoordVec D q₁ + heisCoordVec D q₂ := by
  rcases q₁ with ⟨_, u₁, v₁, s₁, rfl⟩
  rcases q₂ with ⟨_, u₂, v₂, s₂, rfl⟩
  have hmul : (⟨fX u₁ * fY v₁ * fz s₁, u₁, v₁, s₁, rfl⟩ : D.heisSubgroup) *
      ⟨fX u₂ * fY v₂ * fz s₂, u₂, v₂, s₂, rfl⟩ =
      ⟨fX (u₁ + u₂) * fY (v₁ + v₂) * fz (s₁ + s₂ - fB u₂ v₁),
        u₁ + u₂, v₁ + v₂, s₁ + s₂ - fB u₂ v₁, rfl⟩ :=
    Subtype.ext (D.mul_normalForm u₁ v₁ u₂ v₂ s₁ s₂)
  rw [hmul, heisCoordVec_mk, heisCoordVec_mk, heisCoordVec_mk]
  rfl

private theorem heisCoordVec_pow {G : Type*} [Group G]
    {fX fY : (Fin 3 → ZMod 3) → G} {fz : ZMod 3 → G}
    {fB : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3) → ZMod 3}
    (D : PolarizedHeisenbergData fX fY fz fB) (q : D.heisSubgroup) (k : ℕ) :
    heisCoordVec D (q ^ k) = (k : ZMod 3) • heisCoordVec D q := by
  rw [Nat.cast_smul_eq_nsmul]
  induction k with
  | zero => rw [pow_zero, heisCoordVec_one, zero_nsmul]
  | succ k ih => rw [pow_succ, heisCoordVec_mul, ih, succ_nsmul]

private theorem heisCoordVec_conj {G : Type*} [Group G]
    {fX fY : (Fin 3 → ZMod 3) → G} {fz : ZMod 3 → G}
    {fB : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3) → ZMod 3}
    (D : PolarizedHeisenbergData fX fY fz fB) (q u : D.heisSubgroup) :
    heisCoordVec D (q * u * q⁻¹) = heisCoordVec D u := by
  apply add_right_cancel (b := heisCoordVec D q)
  rw [← heisCoordVec_mul, inv_mul_cancel_right, heisCoordVec_mul, add_comm (heisCoordVec D q)]

private theorem heisCoordVec_eq_zero_iff {G : Type*} [Group G]
    {fX fY : (Fin 3 → ZMod 3) → G} {fz : ZMod 3 → G}
    {fB : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3) → ZMod 3}
    (D : PolarizedHeisenbergData fX fY fz fB) (q : D.heisSubgroup) :
    heisCoordVec D q = 0 ↔ q ∈ D.centerSubgroup := by
  rcases q with ⟨_, u, v, s, rfl⟩
  rw [heisCoordVec_mk, D.mem_centerSubgroup_iff, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]

private def heisImageAddSubgroup {G : Type*} [Group G]
    {fX fY : (Fin 3 → ZMod 3) → G} {fz : ZMod 3 → G}
    {fB : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3) → ZMod 3}
    (D : PolarizedHeisenbergData fX fY fz fB) (W : Subgroup D.heisSubgroup) :
    AddSubgroup Fi22Vec where
  carrier := {w | ∃ q ∈ W, heisCoordVec D q = w}
  zero_mem' := ⟨1, W.one_mem, heisCoordVec_one D⟩
  add_mem' := by
    rintro _ _ ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, rfl⟩
    exact ⟨q₁ * q₂, W.mul_mem hq₁ hq₂, heisCoordVec_mul D q₁ q₂⟩
  neg_mem' := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨q⁻¹, W.inv_mem hq, ?_⟩
    apply add_left_cancel (a := heisCoordVec D q)
    rw [← heisCoordVec_mul, mul_inv_cancel, heisCoordVec_one, add_neg_cancel]

end GroupAction

section CoverBound

private theorem prodX_fin3 {G : Type*} [Group G] (p₀ p₁ p₂ : G) (u : Fin 3 → ZMod 3) :
    RootHeisenbergData.prodX (fun i (a : ZMod 3) => (![p₀, p₁, p₂] i) ^ a.val) u =
      p₀ ^ (u 0).val * (p₁ ^ (u 1).val * (p₂ ^ (u 2).val * 1)) :=
  rfl

private theorem prodY_fin3 {G : Type*} [Group G] (q₀ q₁ q₂ : G) (v : Fin 3 → ZMod 3) :
    RootHeisenbergData.prodY (fun i (b : ZMod 3) => (![q₀, q₁, q₂] i) ^ b.val) v =
      q₀ ^ (v 0).val * (q₁ ^ (v 1).val * (q₂ ^ (v 2).val * 1)) :=
  rfl

private theorem conj_eq_of_mul₁ {G : Type*} [Group G] {g a b : G} (h : g * a = b * g) :
    MulAut.conj g a = b := by
  rw [MulAut.conj_apply, h, mul_inv_cancel_right]

private theorem conj_eq_of_mul₂ {G : Type*} [Group G] {g a b₁ b₂ : G}
    (h : g * a = b₁ * (b₂ * g)) :
    MulAut.conj g a = b₁ * b₂ := by
  rw [MulAut.conj_apply, h]; group

private theorem conj_eq_of_mul₄ {G : Type*} [Group G] {g a b₁ b₂ b₃ b₄ : G}
    (h : g * a = b₁ * (b₂ * (b₃ * (b₄ * g)))) :
    MulAut.conj g a = b₁ * b₂ * b₃ * b₄ := by
  rw [MulAut.conj_apply, h]; group

private theorem conj_eq_of_mul₅ {G : Type*} [Group G] {g a b₁ b₂ b₃ b₄ b₅ : G}
    (h : g * a = b₁ * (b₂ * (b₃ * (b₄ * (b₅ * g))))) :
    MulAut.conj g a = b₁ * b₂ * b₃ * b₄ * b₅ := by
  rw [MulAut.conj_apply, h]; group

private theorem conj_heis_of_gens {G : Type*} [Group G] {p₀ p₁ p₂ q₀ q₁ q₂ z : G}
    (D : PolarizedHeisenbergData
      (RootHeisenbergData.prodX (fun i (a : ZMod 3) => (![p₀, p₁, p₂] i) ^ a.val))
      (RootHeisenbergData.prodY (fun i (b : ZMod 3) => (![q₀, q₁, q₂] i) ^ b.val))
      (fun (s : ZMod 3) => z ^ s.val)
      (RootHeisenbergData.pairB (fun _ : Fin 3 => (1 : ZMod 3))))
    {g : G} {P₀' P₁' P₂' Q₀' Q₁' Q₂' Z' : D.heisSubgroup}
    (hp₀ : MulAut.conj g p₀ = P₀'.1) (hp₁ : MulAut.conj g p₁ = P₁'.1)
    (hp₂ : MulAut.conj g p₂ = P₂'.1) (hq₀ : MulAut.conj g q₀ = Q₀'.1)
    (hq₁ : MulAut.conj g q₁ = Q₁'.1) (hq₂ : MulAut.conj g q₂ = Q₂'.1)
    (hz : MulAut.conj g z = Z'.1) (hZ' : heisCoordVec D Z' = 0) :
    ∃ hg : ∀ q ∈ D.heisSubgroup, g * q * g⁻¹ ∈ D.heisSubgroup,
      ∀ q : D.heisSubgroup,
        heisCoordVec D ⟨g * (q : G) * g⁻¹, hg q.1 q.2⟩ =
          fi22LinComb (heisCoordVec D P₀') (heisCoordVec D P₁') (heisCoordVec D P₂')
            (heisCoordVec D Q₀') (heisCoordVec D Q₁') (heisCoordVec D Q₂')
            (heisCoordVec D q) := by
  have hmain : ∀ u v : Fin 3 → ZMod 3, ∀ s : ZMod 3,
      ∃ q' : D.heisSubgroup,
        g * (RootHeisenbergData.prodX (fun i (a : ZMod 3) => (![p₀, p₁, p₂] i) ^ a.val) u *
          RootHeisenbergData.prodY (fun i (b : ZMod 3) => (![q₀, q₁, q₂] i) ^ b.val) v *
          (fun (s : ZMod 3) => z ^ s.val) s) * g⁻¹ = q'.1 ∧
        heisCoordVec D q' =
          fi22LinComb (heisCoordVec D P₀') (heisCoordVec D P₁') (heisCoordVec D P₂')
            (heisCoordVec D Q₀') (heisCoordVec D Q₁') (heisCoordVec D Q₂') (u, v) := by
    intro u v s
    refine ⟨(P₀' ^ (u 0).val * (P₁' ^ (u 1).val * (P₂' ^ (u 2).val * 1))) *
      (Q₀' ^ (v 0).val * (Q₁' ^ (v 1).val * (Q₂' ^ (v 2).val * 1))) * Z' ^ s.val, ?_, ?_⟩
    · dsimp only
      rw [prodX_fin3, prodY_fin3, ← MulAut.conj_apply]
      simp only [map_mul, map_pow, map_one, hp₀, hp₁, hp₂, hq₀, hq₁, hq₂, hz,
        Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one]
    · simp only [heisCoordVec_mul, heisCoordVec_pow, heisCoordVec_one, hZ',
        ZMod.natCast_zmod_val, smul_zero, add_zero, fi22LinComb]
      abel
  have hg : ∀ q ∈ D.heisSubgroup, g * q * g⁻¹ ∈ D.heisSubgroup := by
    rintro _ ⟨u, v, s, rfl⟩
    obtain ⟨q', hq', _⟩ := hmain u v s
    rw [hq']
    exact q'.2
  refine ⟨hg, ?_⟩
  rintro ⟨_, u, v, s, rfl⟩
  obtain ⟨q', hq', hcoord⟩ := hmain u v s
  have heq : (⟨g * (RootHeisenbergData.prodX (fun i (a : ZMod 3) => (![p₀, p₁, p₂] i) ^ a.val) u *
      RootHeisenbergData.prodY (fun i (b : ZMod 3) => (![q₀, q₁, q₂] i) ^ b.val) v *
      (fun (s : ZMod 3) => z ^ s.val) s) * g⁻¹,
      hg _ ⟨u, v, s, rfl⟩⟩ : D.heisSubgroup) = q' :=
    Subtype.ext hq'
  rw [heisCoordVec_mk, ← hcoord, ← heq]

private theorem index_ge_162_of_cover {G S : Type*} [Group G] [Finite G]
    [Group S] [Finite S] [IsSimpleGroup S]
    (f : G →* S) (hf : Function.Injective f)
    {p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n : G}
    (hcov : Fi22CoverData p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n)
    (hnp₂ : n * p₂ = p₀ * n)
    (hnq₂ : n * q₂ = p₀ * (q₀ * (z * (z * n))))
    {H : Subgroup S} (hH : H ≠ ⊤) :
    162 ≤ H.index := by
  have hy : ∀ i : Fin 3, (![q₀, q₁, q₂] i) ^ 3 = 1 := by
    intro i; fin_cases i
    · exact hcov.hq₀
    · exact hcov.hq₁
    · exact hcov.hq₂
  have R : RootHeisenbergData (fun i (a : ZMod 3) => (![p₀, p₁, p₂] i) ^ a.val)
      (fun i (b : ZMod 3) => (![q₀, q₁, q₂] i) ^ b.val)
      (fun (s : ZMod 3) => z ^ s.val)
      (fun _ : Fin 3 => (1 : ZMod 3)) :=
    rootHeisenbergData_of_heisCfg (MulEquiv.refl G) hcov.heis hy
  have D := R.toPolarizedHeisenbergData
  let elP0 : D.heisSubgroup := ⟨_, fi22E0, 0, 0, rfl⟩
  let elP1 : D.heisSubgroup := ⟨_, fi22E1, 0, 0, rfl⟩
  let elP2 : D.heisSubgroup := ⟨_, fi22E2, 0, 0, rfl⟩
  let elQ0 : D.heisSubgroup := ⟨_, 0, fi22E0, 0, rfl⟩
  let elQ1 : D.heisSubgroup := ⟨_, 0, fi22E1, 0, rfl⟩
  let elQ2 : D.heisSubgroup := ⟨_, 0, fi22E2, 0, rfl⟩
  let elZ : D.heisSubgroup := ⟨_, 0, 0, 1, rfl⟩
  have helP0 : elP0.1 = p₀ := by
    change
      RootHeisenbergData.prodX _ fi22E0 * RootHeisenbergData.prodY _ 0 * z ^ (0 : ZMod 3).val = p₀
    rw [prodX_fin3, prodY_fin3]; simp [fi22E0, zmod3_val_one]
  have helP1 : elP1.1 = p₁ := by
    change
      RootHeisenbergData.prodX _ fi22E1 * RootHeisenbergData.prodY _ 0 * z ^ (0 : ZMod 3).val = p₁
    rw [prodX_fin3, prodY_fin3]; simp [fi22E1, zmod3_val_one]
  have helP2 : elP2.1 = p₂ := by
    change
      RootHeisenbergData.prodX _ fi22E2 * RootHeisenbergData.prodY _ 0 * z ^ (0 : ZMod 3).val = p₂
    rw [prodX_fin3, prodY_fin3]; simp [fi22E2, zmod3_val_one]
  have helQ0 : elQ0.1 = q₀ := by
    change
      RootHeisenbergData.prodX _ 0 * RootHeisenbergData.prodY _ fi22E0 * z ^ (0 : ZMod 3).val = q₀
    rw [prodX_fin3, prodY_fin3]; simp [fi22E0, zmod3_val_one]
  have helQ1 : elQ1.1 = q₁ := by
    change
      RootHeisenbergData.prodX _ 0 * RootHeisenbergData.prodY _ fi22E1 * z ^ (0 : ZMod 3).val = q₁
    rw [prodX_fin3, prodY_fin3]; simp [fi22E1, zmod3_val_one]
  have helQ2 : elQ2.1 = q₂ := by
    change
      RootHeisenbergData.prodX _ 0 * RootHeisenbergData.prodY _ fi22E2 * z ^ (0 : ZMod 3).val = q₂
    rw [prodX_fin3, prodY_fin3]; simp [fi22E2, zmod3_val_one]
  have helZ : elZ.1 = z := by
    change RootHeisenbergData.prodX _ 0 * RootHeisenbergData.prodY _ 0 * z ^ (1 : ZMod 3).val = z
    rw [prodX_fin3, prodY_fin3]; simp [zmod3_val_one]
  have hcP0 : heisCoordVec D elP0 = bP0 := heisCoordVec_mk D fi22E0 0 0
  have hcP1 : heisCoordVec D elP1 = bP1 := heisCoordVec_mk D fi22E1 0 0
  have hcP2 : heisCoordVec D elP2 = bP2 := heisCoordVec_mk D fi22E2 0 0
  have hcQ0 : heisCoordVec D elQ0 = bQ0 := heisCoordVec_mk D 0 fi22E0 0
  have hcQ1 : heisCoordVec D elQ1 = bQ1 := heisCoordVec_mk D 0 fi22E1 0
  have hcQ2 : heisCoordVec D elQ2 = bQ2 := heisCoordVec_mk D 0 fi22E2 0
  have hcZ : heisCoordVec D elZ = 0 := heisCoordVec_mk D 0 0 1
  have htwo_smul : ∀ w : Fi22Vec, w + w = (2 : ZMod 3) • w := fun w => by
    rw [← two_smul ℕ w, ← Nat.cast_smul_eq_nsmul (ZMod 3) 2 w]; rfl
  obtain ⟨hdA_norm, hdA_act⟩ := conj_heis_of_gens D (g := dA)
    (P₀' := elP0 * elP0) (P₁' := elP1) (P₂' := elP2 * elP2)
    (Q₀' := elQ0 * elQ0 * elZ * elZ) (Q₁' := elQ1) (Q₂' := elQ2 * elQ2 * elZ * elZ) (Z' := elZ)
    (by rw [conj_eq_of_mul₂ hcov.dAp₀]; simp [helP0])
    (by rw [conj_eq_of_mul₁ hcov.dAp₁, helP1])
    (by rw [conj_eq_of_mul₂ hcov.dAp₂]; simp [helP2])
    (by rw [conj_eq_of_mul₄ hcov.dAq₀]; simp [helQ0, helZ])
    (by rw [conj_eq_of_mul₁ hcov.dAq₁, helQ1])
    (by rw [conj_eq_of_mul₄ hcov.dAq₂]; simp [helQ2, helZ])
    (by rw [conj_eq_of_mul₁ hcov.dAz, helZ]) hcZ
  have hdA_coord : ∀ q : D.heisSubgroup,
      heisCoordVec D ⟨dA * (q : G) * dA⁻¹, hdA_norm q.1 q.2⟩ = fi22ActDA (heisCoordVec D q) := by
    intro q
    rw [hdA_act]
    simp only [heisCoordVec_mul, hcP0, hcP1, hcP2, hcQ0, hcQ1, hcQ2, hcZ, add_zero, htwo_smul,
      fi22ActDA]
  obtain ⟨hn_norm, hn_act⟩ := conj_heis_of_gens D (g := n)
    (P₀' := elP1 * elP1) (P₁' := elQ2) (P₂' := elP0)
    (Q₀' := elP1 * elQ1 * elQ1 * elZ * elZ) (Q₁' := elP2 * elP2)
    (Q₂' := elP0 * elQ0 * elZ * elZ) (Z' := elZ)
    (by rw [conj_eq_of_mul₂ hcov.np₀]; simp [helP1])
    (by rw [conj_eq_of_mul₁ hcov.np₁, helQ2])
    (by rw [conj_eq_of_mul₁ hnp₂, helP0])
    (by rw [conj_eq_of_mul₅ hcov.nq₀]; simp [helP1, helQ1, helZ])
    (by rw [conj_eq_of_mul₂ hcov.nq₁]; simp [helP2])
    (by rw [conj_eq_of_mul₄ hnq₂]; simp [helP0, helQ0, helZ])
    (by rw [conj_eq_of_mul₁ hcov.nz, helZ]) hcZ
  have hn_coord : ∀ q : D.heisSubgroup,
      heisCoordVec D ⟨n * (q : G) * n⁻¹, hn_norm q.1 q.2⟩ = fi22ActN (heisCoordVec D q) := by
    intro q
    rw [hn_act]
    simp only [heisCoordVec_mul, hcP0, hcP1, hcP2, hcQ0, hcQ1, hcQ2, hcZ, add_zero,
      add_assoc, htwo_smul, fi22ActN]
  have hZne : D.centerSubgroup.map D.heisSubgroup.subtype ≠ ⊥ := by
    intro hbot
    exact D.centerSubgroup_ne_bot
      ((Subgroup.map_eq_bot_iff_of_injective _ D.heisSubgroup.subtype_injective).mp hbot)
  have hV : ∀ u : Fin 3 → ZMod 3, 3 • u = 0 := fun u => by
    ext i; change 3 • u i = 0; rw [nsmul_eq_mul, CharP.cast_eq_zero (ZMod 3) 3, zero_mul]
  have hcardV : Nat.card (Fin 3 → ZMod 3) = 27 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]; rfl
  have hcardQ : Nat.card D.heisSubgroup = 2187 := by
    rw [← Nat.card_congr D.heisEquiv, Nat.card_prod, Nat.card_prod, hcardV, Nat.card_zmod]
  have hcardZ : Nat.card D.centerSubgroup = 3 := by
    rw [← Nat.card_congr D.centerEquiv, Nat.card_zmod]
  refine le_index_of_injective_of_forall_not_le_index hH f hf hZne
    fun K hZK => ?_
  have hZK' : ¬ D.centerSubgroup ≤ K.subgroupOf D.heisSubgroup := fun hle =>
    hZK (by rintro _ ⟨z₀, hz₀, rfl⟩; exact hle hz₀)
  set W : Subgroup D.heisSubgroup := K.subgroupOf D.heisSubgroup
  have h81 : 81 ≤ W.index := by
    have hle := mul_le_index_of_not_le
      D.centerSubgroup_le_center D.commutator_mem_centerSubgroup
      (fun _ hq => D.pow_p_eq_one_of_mem_centerSubgroup hq)
      (D.pow_p_mem_centerSubgroup hV)
      (fun _ hq _ hz => D.exists_commutator_eq_of_not_mem hq hz)
      hZK' D.index_centerSubgroup.symm.le
    rwa [hcardV] at hle
  by_cases h1 : ∀ q : D.heisSubgroup, (q : G) * dA ∉ K
  · exact le_trans (by omega : 162 ≤ 2 * W.index)
      (ExtraspecialCoord.two_mul_index_le_of_forall_mul_not_mem hdA_norm h1)
  · push Not at h1
    obtain ⟨q₁, hq₁K⟩ := h1
    by_cases h2 : ∀ q : D.heisSubgroup, (q : G) * n ∉ K
    · exact le_trans (by omega : 162 ≤ 2 * W.index)
        (ExtraspecialCoord.two_mul_index_le_of_forall_mul_not_mem hn_norm h2)
    · push Not at h2
      obtain ⟨q₂, hq₂K⟩ := h2
      by_cases hW_idx : 162 ≤ W.index
      · exact le_trans hW_idx (ExtraspecialCoord.subgroupOf_index_le_index K)
      · push Not at hW_idx
        exfalso
        have hW_mul : W.index * Nat.card W = 2187 := by
          rw [W.index_mul_card, hcardQ]
        have hW_ne1 : Nat.card W ≠ 1 := by
          intro h1
          rw [h1, mul_one] at hW_mul
          omega
        have hW_ne_bot : W ≠ ⊥ := fun hbot => hW_ne1 (by rw [hbot, Subgroup.card_bot])
        obtain ⟨u₀, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW_ne_bot
        set w₀ : D.heisSubgroup := u₀.1
        have hw₀W : w₀ ∈ W := u₀.2
        have hw₀1 : w₀ ≠ 1 := fun h => hu₀1 (Subtype.ext h)
        have hWZ_bot : W ⊓ D.centerSubgroup = ⊥ := by
          let Z' : Subgroup D.centerSubgroup := W.subgroupOf D.centerSubgroup
          have hdvd : Nat.card Z' ∣ 3 := by
            have h := Subgroup.card_subgroup_dvd_card Z'
            rwa [hcardZ] at h
          rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h1 | h3
          · rw [eq_bot_iff]
            intro x hx
            have hxZ' : (⟨x, hx.2⟩ : D.centerSubgroup) ∈ Z' := hx.1
            have hbot : Z' = ⊥ := Subgroup.card_eq_one.mp h1
            rw [hbot, Subgroup.mem_bot] at hxZ'
            exact congrArg Subtype.val hxZ'
          · exfalso
            apply hZK'
            have htop : Z' = ⊤ := Subgroup.eq_top_of_card_eq Z' (h3.trans hcardZ.symm)
            intro z₀ hz₀
            have hz' : (⟨z₀, hz₀⟩ : D.centerSubgroup) ∈ Z' := htop ▸ mem_top _
            exact hz'
        have hw₀_coord : heisCoordVec D w₀ ≠ 0 := by
          intro h0
          have hw₀Z : w₀ ∈ W ⊓ D.centerSubgroup := ⟨hw₀W, (heisCoordVec_eq_zero_iff D w₀).mp h0⟩
          rw [hWZ_bot, Subgroup.mem_bot] at hw₀Z
          exact hw₀1 hw₀Z
        set U := heisImageAddSubgroup D W
        have hUDA : ∀ w ∈ U, fi22ActDA w ∈ U := by
          rintro _ ⟨w, hwW, rfl⟩
          set u₁ : D.heisSubgroup := ⟨dA * (w : G) * dA⁻¹, hdA_norm w.1 w.2⟩
          refine ⟨q₁ * u₁ * q₁⁻¹, ?_, ?_⟩
          · rw [mem_subgroupOf]
            have heq : ((q₁ * u₁ * q₁⁻¹ : D.heisSubgroup) : G) =
                ((q₁ : G) * dA) * (w : G) * ((q₁ : G) * dA)⁻¹ := by
              simp only [u₁, Subgroup.coe_mul, Subgroup.coe_inv]
              group
            rw [heq]
            exact K.mul_mem (K.mul_mem hq₁K hwW) (K.inv_mem hq₁K)
          · rw [heisCoordVec_conj, hdA_coord]
        have hUN : ∀ w ∈ U, fi22ActN w ∈ U := by
          rintro _ ⟨w, hwW, rfl⟩
          set u₂ : D.heisSubgroup := ⟨n * (w : G) * n⁻¹, hn_norm w.1 w.2⟩
          refine ⟨q₂ * u₂ * q₂⁻¹, ?_, ?_⟩
          · rw [mem_subgroupOf]
            have heq : ((q₂ * u₂ * q₂⁻¹ : D.heisSubgroup) : G) =
                ((q₂ : G) * n) * (w : G) * ((q₂ : G) * n)⁻¹ := by
              simp only [u₂, Subgroup.coe_mul, Subgroup.coe_inv]
              group
            rw [heq]
            exact K.mul_mem (K.mul_mem hq₂K hwW) (K.inv_mem hq₂K)
          · rw [heisCoordVec_conj, hn_coord]
        have hsurj : Function.Surjective (fun w : W => heisCoordVec D w.1) := by
          intro y
          have hyU : y ∈ U :=
            fi22_mem_of_invariant hUDA hUN ⟨w₀, hw₀W, rfl⟩ hw₀_coord y
          obtain ⟨w, hwW, rfl⟩ := hyU
          exact ⟨⟨w, hwW⟩, rfl⟩
        have hcard_le : 729 ≤ Nat.card W := by
          have hle := Nat.card_le_card_of_surjective (fun w : W => heisCoordVec D w.1) hsurj
          rwa [Nat.card_prod, hcardV] at hle
        have hmul_ge : 81 * 729 ≤ W.index * Nat.card W := Nat.mul_le_mul h81 hcard_le
        omega

/-- Every proper subgroup of `Fi₂₂` has index at least `162` (and in particular at least `114`). -/
theorem index_ge_Fi22 {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .Fi22) {H : Subgroup S} (hH : H ≠ ⊤) :
    162 ≤ H.index := by
  have : Finite NativeSporadic.Fi22 := Finite.of_equiv S e.toEquiv
  have : Finite J := Finite.of_equiv _ fi22EquivJ.toEquiv
  obtain ⟨p₀, p₁, p₂, q₀, q₁, q₂, z, dA, dB, n, hcov, hnp₂, hnq₂⟩ := fi22_full_cover
  exact index_ge_162_of_cover
    (e.symm.toMonoidHom.comp (fi22EquivJ.symm : J →* NativeSporadic.Fi22))
    (e.symm.injective.comp fi22EquivJ.symm.injective) hcov hnp₂ hnq₂ hH

/-- Theorem 1.1(a) of Maróti (2002) for primitive almost simple groups with socle `Fi₂₂`. -/
theorem sporadicCase_Fi22 {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type)
    [Group S] [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .Fi22)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 64561751654400 :=
    (Nat.card_congr e.toEquiv).trans card_Fi22
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 162) (c := 2) (by decide)
    (fun H hH => index_ge_Fi22 e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.Fi22, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

end CoverBound

end Maroti
