module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Maroti.MinDegree.PolarizedHeisenberg

/-!
# Minimum degree of faithful actions from root-group Heisenberg systems

In a group `G` of Lie type over a finite field `K` of characteristic `p`, suppose we have `m` pairs
of root subgroups `x i, y i : K → G` (`i : Fin m`) and a central root subgroup `z : K → G` with
commutator constants `c : Fin m → K` (`c i ≠ 0`) satisfying three conditions:
* Each `x i`, `y i`, and `z` is additive (`f (a + b) = f a * f b`), and `z a = 1 → a = 0`.
* Elements `x i a` and `x j b` commute, `y i a` and `y j b` commute, and `z b` commutes with
  `x i a` and `y i a`.
* For `i ≠ j`, `x i a` and `y j b` commute, and `⁅x i a, y i b⁆ = z (c i * a * b)`.

Then `X u = ((List.finRange m).map fun i => x i (u i)).prod`,
`Y v = ((List.finRange m).map fun i => y i (v i)).prod`, and `B u v = ∑ i : Fin m, c i * u i * v i`
form a `PolarizedHeisenbergData` on `V = (Fin m → K)`. Consequently, two bounds hold:
* Every faithful action of `G` on a finite type `α` satisfies
  `p * Nat.card K ^ m ≤ Nat.card α`.
* If `G` is a finite simple group, every proper subgroup `H ≠ ⊤` of `G` satisfies
  `p * Nat.card K ^ m ≤ H.index`.
-/

@[expose] public section

namespace Maroti

open Subgroup
open scoped commutatorElement

variable {m : ℕ} {K G : Type*} [Field K] [Group G]

/-- Hypotheses for `m` root-group pairs `(x i, y i)` with central root group `z` and nonzero
commutator constants `c i`. -/
structure RootHeisenbergData (x y : Fin m → K → G) (z : K → G) (c : Fin m → K) : Prop where
  x_add : ∀ i a b, x i (a + b) = x i a * x i b
  y_add : ∀ i a b, y i (a + b) = y i a * y i b
  z_add : ∀ a b, z (a + b) = z a * z b
  z_eq_one : ∀ a, z a = 1 → a = 0
  c_ne_zero : ∀ i, c i ≠ 0
  commute_x_x : ∀ i j a b, Commute (x i a) (x j b)
  commute_y_y : ∀ i j a b, Commute (y i a) (y j b)
  commute_x_z : ∀ i a b, Commute (x i a) (z b)
  commute_y_z : ∀ i a b, Commute (y i a) (z b)
  commute_x_y_of_ne : ∀ i j, i ≠ j → ∀ a b, Commute (x i a) (y j b)
  comm_x_y : ∀ i a b, ⁅x i a, y i b⁆ = z (c i * a * b)

namespace RootHeisenbergData

variable {x y : Fin m → K → G} {z : K → G} {c : Fin m → K} (R : RootHeisenbergData x y z c)

include R in
theorem z_zero : z 0 = 1 := by
  have h := R.z_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

include R in
theorem commute_x_listProd_x (a : Fin m) (t : K) (l : List (Fin m)) (u : Fin m → K) :
    Commute (x a t) ((l.map fun i => x i (u i)).prod) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons]
    exact (R.commute_x_x a b t (u b)).mul_right ih

include R in
theorem commute_y_listProd_y (a : Fin m) (t : K) (l : List (Fin m)) (v : Fin m → K) :
    Commute (y a t) ((l.map fun i => y i (v i)).prod) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons]
    exact (R.commute_y_y a b t (v b)).mul_right ih

include R in
theorem listProd_x_add (l : List (Fin m)) (u₁ u₂ : Fin m → K) :
    ((l.map fun i => x i (u₁ i + u₂ i)).prod) =
      ((l.map fun i => x i (u₁ i)).prod) * ((l.map fun i => x i (u₂ i)).prod) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
      List.map_cons, List.prod_cons, R.x_add, ih]
    have hc := R.commute_x_listProd_x a (u₂ a) l u₁
    calc x a (u₁ a) * x a (u₂ a) *
          ((l.map fun i => x i (u₁ i)).prod * (l.map fun i => x i (u₂ i)).prod)
        = x a (u₁ a) * (x a (u₂ a) * (l.map fun i => x i (u₁ i)).prod) *
            (l.map fun i => x i (u₂ i)).prod := by
          group
      _ = x a (u₁ a) * ((l.map fun i => x i (u₁ i)).prod * x a (u₂ a)) *
            (l.map fun i => x i (u₂ i)).prod := by
          rw [hc.eq]
      _ = (x a (u₁ a) * (l.map fun i => x i (u₁ i)).prod) *
            (x a (u₂ a) * (l.map fun i => x i (u₂ i)).prod) := by
          group

include R in
theorem listProd_y_add (l : List (Fin m)) (v₁ v₂ : Fin m → K) :
    ((l.map fun i => y i (v₁ i + v₂ i)).prod) =
      ((l.map fun i => y i (v₁ i)).prod) * ((l.map fun i => y i (v₂ i)).prod) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
      List.map_cons, List.prod_cons, R.y_add, ih]
    have hc := R.commute_y_listProd_y a (v₂ a) l v₁
    calc y a (v₁ a) * y a (v₂ a) *
          ((l.map fun i => y i (v₁ i)).prod * (l.map fun i => y i (v₂ i)).prod)
        = y a (v₁ a) * (y a (v₂ a) * (l.map fun i => y i (v₁ i)).prod) *
            (l.map fun i => y i (v₂ i)).prod := by
          group
      _ = y a (v₁ a) * ((l.map fun i => y i (v₁ i)).prod * y a (v₂ a)) *
            (l.map fun i => y i (v₂ i)).prod := by
          rw [hc.eq]
      _ = (y a (v₁ a) * (l.map fun i => y i (v₁ i)).prod) *
            (y a (v₂ a) * (l.map fun i => y i (v₂ i)).prod) := by
          group

include R in
theorem commute_listProd_x_z (l : List (Fin m)) (u : Fin m → K) (s : K) :
    Commute ((l.map fun i => x i (u i)).prod) (z s) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons]
    exact (R.commute_x_z a (u a) s).mul_left ih

include R in
theorem commute_listProd_y_z (l : List (Fin m)) (v : Fin m → K) (s : K) :
    Commute ((l.map fun i => y i (v i)).prod) (z s) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons]
    exact (R.commute_y_z a (v a) s).mul_left ih

include R in
theorem comm_x_listProd_y (l : List (Fin m)) (i : Fin m) (a : K) (v : Fin m → K) :
    ⁅x i a, (l.map fun j => y j (v j)).prod⁆ =
      z ((l.map fun j => if i = j then c i * a * v j else 0).sum) := by
  induction l with
  | nil => simp [R.z_zero]
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, R.z_add]
    set P := (l.map fun k => y k (v k)).prod
    set S := (l.map fun k => if i = k then c i * a * v k else 0).sum
    have hc : y j (v j) * z S = z S * y j (v j) := R.commute_y_z j (v j) S
    have hmul : ⁅x i a, y j (v j) * P⁆ = ⁅x i a, y j (v j)⁆ * z S := by
      calc ⁅x i a, y j (v j) * P⁆
          = ⁅x i a, y j (v j)⁆ * (y j (v j) * ⁅x i a, P⁆ * (y j (v j))⁻¹) := by
            simp only [commutatorElement_def]; group
        _ = ⁅x i a, y j (v j)⁆ * (y j (v j) * z S * (y j (v j))⁻¹) := by rw [ih]
        _ = ⁅x i a, y j (v j)⁆ * (z S * y j (v j) * (y j (v j))⁻¹) := by rw [hc]
        _ = ⁅x i a, y j (v j)⁆ * z S := by group
    rw [hmul]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, R.comm_x_y]
    · simp only [hij, ↓reduceIte,
        commutatorElement_eq_one_iff_mul_comm.mpr (R.commute_x_y_of_ne i j hij a (v j)),
        R.z_zero]

/-- Product `X u = ((List.finRange m).map fun i => x i (u i)).prod`. -/
def prodX (x : Fin m → K → G) (u : Fin m → K) : G :=
  ((List.finRange m).map fun i => x i (u i)).prod

/-- Product `Y v = ((List.finRange m).map fun i => y i (v i)).prod`. -/
def prodY (y : Fin m → K → G) (v : Fin m → K) : G :=
  ((List.finRange m).map fun i => y i (v i)).prod

/-- Bilinear pairing `B u v = ∑ i : Fin m, c i * u i * v i`. -/
def pairB (c : Fin m → K) (u v : Fin m → K) : K :=
  ∑ i : Fin m, c i * u i * v i

include R in
theorem comm_listProd_x_prodY (l : List (Fin m)) (u v : Fin m → K) :
    ⁅(l.map fun i => x i (u i)).prod, prodY y v⁆ =
      z ((l.map fun i => c i * u i * v i).sum) := by
  induction l with
  | nil => simp [R.z_zero]
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, R.z_add]
    set P := (l.map fun k => x k (u k)).prod
    set S := (l.map fun k => c k * u k * v k).sum
    have hxY : ⁅x i (u i), prodY y v⁆ = z (c i * u i * v i) := by
      rw [prodY, R.comm_x_listProd_y]
      congr 1
      rw [← Fin.sum_univ_def, Finset.sum_ite_eq]
      simp
    have hc1 : x i (u i) * z S = z S * x i (u i) := R.commute_x_z i (u i) S
    have hc2 : z S * z (c i * u i * v i) = z (c i * u i * v i) * z S := by
      rw [← R.z_add, ← R.z_add, add_comm]
    calc ⁅x i (u i) * P, prodY y v⁆
        = (x i (u i) * ⁅P, prodY y v⁆) * (x i (u i))⁻¹ * ⁅x i (u i), prodY y v⁆ := by
          simp only [commutatorElement_def]; group
      _ = (x i (u i) * z S) * (x i (u i))⁻¹ * z (c i * u i * v i) := by rw [ih, hxY]
      _ = (z S * x i (u i)) * (x i (u i))⁻¹ * z (c i * u i * v i) := by rw [hc1]
      _ = z S * z (c i * u i * v i) := by group
      _ = z (c i * u i * v i) * z S := hc2

include R in
/-- A `RootHeisenbergData` induces a `PolarizedHeisenbergData` on `V = (Fin m → K)`. -/
theorem toPolarizedHeisenbergData :
    PolarizedHeisenbergData (prodX x) (prodY y) z (pairB c) where
  X_add u₁ u₂ := R.listProd_x_add (List.finRange m) u₁ u₂
  Y_add v₁ v₂ := R.listProd_y_add (List.finRange m) v₁ v₂
  z_add := R.z_add
  z_eq_one := R.z_eq_one
  commute_X_z u s := R.commute_listProd_x_z (List.finRange m) u s
  commute_Y_z v s := R.commute_listProd_y_z (List.finRange m) v s
  comm_X_Y u v := by
    rw [prodX, R.comm_listProd_x_prodY, pairB, Fin.sum_univ_def]
  B_add_left u₁ u₂ v := by
    simp only [pairB, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  B_add_right u v₁ v₂ := by
    simp only [pairB, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  B_surj_left u hu s := by
    have hex : ∃ i, u i ≠ 0 := by
      by_contra! h
      exact hu (funext h)
    obtain ⟨i₀, hi₀⟩ := hex
    refine ⟨Pi.single i₀ ((c i₀)⁻¹ * (u i₀)⁻¹ * s), ?_⟩
    unfold pairB
    rw [Finset.sum_eq_single i₀]
    · rw [Pi.single_eq_same]
      have hc0 := R.c_ne_zero i₀
      calc c i₀ * u i₀ * ((c i₀)⁻¹ * (u i₀)⁻¹ * s)
          = (c i₀ * (c i₀)⁻¹) * (u i₀ * (u i₀)⁻¹) * s := by ring
        _ = s := by rw [mul_inv_cancel₀ hc0, mul_inv_cancel₀ hi₀, one_mul, one_mul]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, mul_zero]
    · intro h
      exact False.elim (h (Finset.mem_univ i₀))
  B_surj_right v hv s := by
    have hex : ∃ i, v i ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    obtain ⟨i₀, hi₀⟩ := hex
    refine ⟨Pi.single i₀ ((c i₀)⁻¹ * (v i₀)⁻¹ * s), ?_⟩
    unfold pairB
    rw [Finset.sum_eq_single i₀]
    · rw [Pi.single_eq_same]
      have hc0 := R.c_ne_zero i₀
      calc c i₀ * ((c i₀)⁻¹ * (v i₀)⁻¹ * s) * v i₀
          = (c i₀ * (c i₀)⁻¹) * (v i₀ * (v i₀)⁻¹) * s := by ring
        _ = s := by rw [mul_inv_cancel₀ hc0, mul_inv_cancel₀ hi₀, one_mul, one_mul]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, mul_zero, zero_mul]
    · intro h
      exact False.elim (h (Finset.mem_univ i₀))

include R in
/-- If `G` acts faithfully on a finite type `α`, then
`p * Nat.card K ^ m ≤ Nat.card α`. -/
theorem mul_pow_le_card_of_faithfulSMul [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {α : Type*} [Finite α] [MulAction G α] [FaithfulSMul G α] :
    p * Nat.card K ^ m ≤ Nat.card α := by
  have hV : ∀ u : Fin m → K, p • u = 0 := fun u => by
    ext i
    change p • u i = 0
    rw [nsmul_eq_mul, CharP.cast_eq_zero K p, zero_mul]
  have hcard : Nat.card (Fin m → K) = Nat.card K ^ m := by
    rw [Nat.card_fun, Nat.card_fin]
  rw [← hcard]
  exact R.toPolarizedHeisenbergData.mul_card_le_card_of_faithfulSMul hV

include R in
/-- If `G` is a finite simple group, every proper subgroup `H ≠ ⊤` of `G` has index
`p * Nat.card K ^ m ≤ H.index`. -/
theorem mul_pow_le_index_of_ne_top [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    [Finite G] [IsSimpleGroup G] {H : Subgroup G} (hH : H ≠ ⊤) :
    p * Nat.card K ^ m ≤ H.index := by
  have : FaithfulSMul G (G ⧸ H) := faithfulSMul_quotient_of_ne_top hH
  exact R.mul_pow_le_card_of_faithfulSMul (α := G ⧸ H)

end RootHeisenbergData

end Maroti
