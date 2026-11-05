module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Ring

/-!
# Lemma 2.1 of Maróti (2002)

This file proves Lemma 2.1 of A. Maróti, *On the orders of primitive groups*,
J. Algebra 258 (2002), pages 635–636 (`Maroti.lemma_2_1`). For integers `a, b` and `m` such that
`8 ≤ m`, `2 ≤ a`, `2 ≤ b`, and `m = a * b`, the inequality
`m! ≤ (m! / (b! ^ a * a!)) ^ ⌊log₂ (m! / (b! ^ a * a!))⌋` holds.

Instead of the prime counting estimates used in the paper, the proof establishes an elementary
lower bound on `N(a, b) = (a * b)! / (b! ^ a * a!)`. Induction on `k` shows that
`3 ^ k ≤ (2 * k + 1).choose k` (`three_pow_le_choose_two_mul_add_one`), and monotonicity of
binomial coefficients gives `(a + 1) * 3 ^ (b - 1) ≤ ((a + 1) * b).choose b` for `1 ≤ a` and
`1 ≤ b` (`mul_three_pow_le_choose`). From the identity
`((a + 1) * b)! = ((a + 1) * b).choose b * b! * (a * b)!`, induction on `a` gives
`3 ^ ((a - 1) * (b - 1)) ≤ N(a, b)` (`three_pow_mul_le_factorial_mul`). Because
`2 * ((a * b + 1) / 2) ≤ 3 * ((a - 1) * (b - 1))` for `8 ≤ a * b` and `2 ^ 3 ≤ 3 ^ 2`, we obtain
`2 ^ ((m + 1) / 2) ≤ N(a, b)` (`two_pow_half_le_quotient`). Combining this with the upper bound
`m! ≤ 2 ^ (((m + 1) / 2) ^ 2)` for `7 ≤ m` (`factorial_le_two_pow_sq_half`) proves `lemma_2_1`.
-/

@[expose] public section

namespace Maroti

open scoped Nat

/-- For all `k : ℕ`, `3 ^ k ≤ (2 * k + 1).choose k`. -/
private theorem three_pow_le_choose_two_mul_add_one (k : ℕ) :
    3 ^ k ≤ (2 * k + 1).choose k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (2 * k + 2).choose (k + 1) * (k + 1) = (2 * k + 2) * (2 * k + 1).choose k := by
      have := (Nat.add_one_mul_choose_eq (2 * k + 1) k).symm
      simpa [Nat.add_assoc] using this
    have h2 : (2 * (k + 1) + 1).choose (k + 1) * (k + 2) =
        (2 * k + 3) * (2 * k + 2).choose (k + 1) := by
      have h_id := (Nat.add_one_mul_choose_eq (2 * k + 2) (k + 1)).symm
      have h_symm1 : (2 * k + 2 + 1).choose (k + 1 + 1) = (2 * (k + 1) + 1).choose (k + 1) := by
        rw [← Nat.choose_symm (by omega : k + 1 + 1 ≤ 2 * k + 2 + 1)]
        congr 1
        omega
      rw [h_symm1] at h_id
      simpa [Nat.add_assoc] using h_id
    have h3 : (2 * (k + 1) + 1).choose (k + 1) * ((k + 1) * (k + 2)) =
        (2 * k + 3) * (2 * k + 2) * (2 * k + 1).choose k := by
      calc (2 * (k + 1) + 1).choose (k + 1) * ((k + 1) * (k + 2))
        _ = (2 * (k + 1) + 1).choose (k + 1) * (k + 2) * (k + 1) := by ring
        _ = (2 * k + 3) * (2 * k + 2).choose (k + 1) * (k + 1) := by rw [h2]
        _ = (2 * k + 3) * ((2 * k + 2).choose (k + 1) * (k + 1)) := by ring
        _ = (2 * k + 3) * ((2 * k + 2) * (2 * k + 1).choose k) := by rw [h1]
        _ = (2 * k + 3) * (2 * k + 2) * (2 * k + 1).choose k := by ring
    have hcoef : 3 * ((k + 1) * (k + 2)) ≤ (2 * k + 3) * (2 * k + 2) := by
      have : 3 * ((k + 1) * (k + 2)) + k * k + k = (2 * k + 3) * (2 * k + 2) := by ring
      omega
    have hpos : 0 < (k + 1) * (k + 2) := Nat.mul_pos (by omega) (by omega)
    apply Nat.le_of_mul_le_mul_right _ hpos
    calc 3 ^ (k + 1) * ((k + 1) * (k + 2))
      _ = 3 * ((k + 1) * (k + 2)) * 3 ^ k := by ring
      _ ≤ (2 * k + 3) * (2 * k + 2) * (2 * k + 1).choose k := Nat.mul_le_mul hcoef ih
      _ = (2 * (k + 1) + 1).choose (k + 1) * ((k + 1) * (k + 2)) := h3.symm

/-- For `1 ≤ a` and `1 ≤ b`, `(a + 1) * 3 ^ (b - 1) ≤ ((a + 1) * b).choose b`. -/
private theorem mul_three_pow_le_choose {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a + 1) * 3 ^ (b - 1) ≤ ((a + 1) * b).choose b := by
  cases b with
  | zero => omega
  | succ k =>
    simp only [Nat.add_sub_cancel]
    have h_id : ((a + 1) * (k + 1)).choose (k + 1) * (k + 1) =
        (a + 1) * (k + 1) * ((a + 1) * (k + 1) - 1).choose k := by
      have heq : (a + 1) * (k + 1) - 1 + 1 = (a + 1) * (k + 1) := by
        have : 1 * 1 ≤ (a + 1) * (k + 1) := Nat.mul_le_mul (by omega) (by omega)
        omega
      have := (Nat.add_one_mul_choose_eq ((a + 1) * (k + 1) - 1) k).symm
      rwa [heq] at this
    have h_mono : (2 * k + 1).choose k ≤ ((a + 1) * (k + 1) - 1).choose k := by
      apply Nat.choose_le_choose k
      have : 2 * (k + 1) ≤ (a + 1) * (k + 1) := Nat.mul_le_mul_right (k + 1) (by omega)
      omega
    have h_3k : 3 ^ k ≤ ((a + 1) * (k + 1) - 1).choose k :=
      (three_pow_le_choose_two_mul_add_one k).trans h_mono
    apply Nat.le_of_mul_le_mul_right _ (by omega : 0 < k + 1)
    rw [h_id]
    calc (a + 1) * 3 ^ k * (k + 1)
      _ = (a + 1) * (k + 1) * 3 ^ k := by ring
      _ ≤ (a + 1) * (k + 1) * ((a + 1) * (k + 1) - 1).choose k :=
        Nat.mul_le_mul_left _ h_3k

/-- For `1 ≤ a` and `1 ≤ b`, `3 ^ ((a - 1) * (b - 1)) * ((b !) ^ a * a !) ≤ (a * b)!`. -/
private theorem three_pow_mul_le_factorial_mul {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    3 ^ ((a - 1) * (b - 1)) * ((b !) ^ a * a !) ≤ (a * b)! := by
  cases a with
  | zero => omega
  | succ k =>
    simp only [Nat.add_sub_cancel]
    induction k with
    | zero =>
      simp
    | succ k ih =>
      have ih' := ih (by omega)
      have h_choose : ((k + 2) * b).choose b * b ! * ((k + 1) * b)! = ((k + 2) * b)! := by
        have hle : b ≤ (k + 2) * b := by
          calc b = 1 * b := (Nat.one_mul b).symm
            _ ≤ (k + 2) * b := Nat.mul_le_mul_right b (by omega)
        have hsub : (k + 2) * b - b = (k + 1) * b := by
          have : (k + 2) * b = (k + 1) * b + b := by ring
          omega
        have := Nat.choose_mul_factorial_mul_factorial hle
        rwa [hsub] at this
      have h_step := mul_three_pow_le_choose (a := k + 1) (b := b) (by omega) hb
      calc 3 ^ ((k + 1) * (b - 1)) * ((b !) ^ (k + 2) * (k + 2)!)
        _ = ((k + 2) * 3 ^ (b - 1)) * b ! *
              (3 ^ (k * (b - 1)) * ((b !) ^ (k + 1) * (k + 1)!)) := by
          rw [Nat.add_mul k 1 (b - 1), Nat.one_mul, Nat.pow_add,
            Nat.pow_succ (b !) (k + 1), Nat.factorial_succ (k + 1)]
          ring
        _ ≤ ((k + 2) * b).choose b * b ! * ((k + 1) * b)! := by
          apply Nat.mul_le_mul _ ih'
          exact Nat.mul_le_mul_right (b !) h_step
        _ = ((k + 2) * b)! := h_choose

/-- For `2 ≤ a`, `2 ≤ b` with `8 ≤ a * b`, `2 * ((a * b + 1) / 2) ≤ 3 * ((a - 1) * (b - 1))`. -/
private theorem two_mul_half_le_three_mul_sub {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hm : 8 ≤ a * b) :
    2 * ((a * b + 1) / 2) ≤ 3 * ((a - 1) * (b - 1)) := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, b = d + 2 := ⟨b - 2, by omega⟩
  have hsub1 : c + 2 - 1 = c + 1 := by omega
  have hsub2 : d + 2 - 1 = d + 1 := by omega
  rw [hsub1, hsub2]
  have hcd : 2 ≤ c + d := by
    by_contra h
    rcases c with _ | _ | c <;> rcases d with _ | _ | d <;> omega
  have hprod : (c + 2) * (d + 2) + 1 + 2 * c * d + c + d = 3 * ((c + 1) * (d + 1)) + 2 := by ring
  omega

/-- For `2 ≤ a`, `2 ≤ b` with `8 ≤ a * b`,
`2 ^ ((a * b + 1) / 2) ≤ (a * b)! / ((b !) ^ a * a !)`. -/
private theorem two_pow_half_le_quotient {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hm : 8 ≤ a * b) :
    2 ^ ((a * b + 1) / 2) ≤ (a * b)! / ((b !) ^ a * a !) := by
  have h3 : 3 ^ ((a - 1) * (b - 1)) ≤ (a * b)! / ((b !) ^ a * a !) := by
    rw [Nat.le_div_iff_mul_le
      (Nat.mul_pos (Nat.pow_pos (Nat.factorial_pos b)) (Nat.factorial_pos a))]
    exact three_pow_mul_le_factorial_mul (by omega) (by omega)
  suffices h23 : 2 ^ ((a * b + 1) / 2) ≤ 3 ^ ((a - 1) * (b - 1)) from h23.trans h3
  have hexp := two_mul_half_le_three_mul_sub ha hb hm
  set X := (a * b + 1) / 2
  set Y := (a - 1) * (b - 1)
  have hpow : (2 ^ X) ^ 2 ≤ (3 ^ Y) ^ 2 := by
    calc (2 ^ X) ^ 2
      _ = 2 ^ (2 * X) := by rw [Nat.mul_comm 2 X, Nat.pow_mul]
      _ ≤ 2 ^ (3 * Y) := Nat.pow_le_pow_right (by decide) hexp
      _ = (2 ^ 3) ^ Y := by rw [Nat.pow_mul]
      _ ≤ (3 ^ 2) ^ Y := Nat.pow_le_pow_left (by decide : 2 ^ 3 ≤ 3 ^ 2) Y
      _ = (3 ^ Y) ^ 2 := by rw [← Nat.pow_mul, Nat.mul_comm 2 Y, Nat.pow_mul]
  by_contra hlt
  have hlt' : 3 ^ Y < 2 ^ X := Nat.lt_of_not_le hlt
  have hpow_lt : (3 ^ Y) ^ 2 < (2 ^ X) ^ 2 := Nat.pow_lt_pow_left hlt' (by decide)
  omega

/-- For `4 ≤ k`, `(2 * k + 2) * (2 * k + 1) ≤ 2 ^ (2 * k + 1)`. -/
private theorem mul_two_add_le_two_pow {k : ℕ} (hk : 4 ≤ k) :
    (2 * k + 2) * (2 * k + 1) ≤ 2 ^ (2 * k + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
  induction j with
  | zero => decide
  | succ j ihj =>
    have h1 : (2 * (j + 1 + 4) + 2) * (2 * (j + 1 + 4) + 1) ≤
        4 * ((2 * (j + 4) + 2) * (2 * (j + 4) + 1)) := by
      have : (2 * (j + 1 + 4) + 2) * (2 * (j + 1 + 4) + 1) +
          (12 * j * j + 106 * j + 228) =
          4 * ((2 * (j + 4) + 2) * (2 * (j + 4) + 1)) := by ring
      omega
    have h2 : 4 * ((2 * (j + 4) + 2) * (2 * (j + 4) + 1)) ≤
        2 ^ (2 * (j + 1 + 4) + 1) := by
      have heq : 2 ^ (2 * (j + 1 + 4) + 1) = 4 * 2 ^ (2 * (j + 4) + 1) := by
        have : 2 * (j + 1 + 4) + 1 = (2 * (j + 4) + 1) + 2 := by omega
        rw [this, Nat.pow_add, Nat.mul_comm]
      rw [heq]
      exact Nat.mul_le_mul_left 4 (ihj (by omega))
    exact h1.trans h2

/-- For `7 ≤ m`, `m ! ≤ 2 ^ (((m + 1) / 2) ^ 2)`. -/
theorem factorial_le_two_pow_sq_half {m : ℕ} (hm : 7 ≤ m) :
    m ! ≤ 2 ^ (((m + 1) / 2) ^ 2) := by
  obtain ⟨d, rfl⟩ : ∃ d, m = d + 7 := ⟨m - 7, by omega⟩
  clear hm
  induction d using Nat.strong_induction_on with
  | h d ih =>
    rcases d with _ | _ | d
    · decide
    · decide
    · have ih' := ih d (by omega)
      set m₀ := d + 7
      set k := (m₀ + 1) / 2
      have hk : 4 ≤ k := by omega
      have h_k_succ : (d + 2 + 7 + 1) / 2 = k + 1 := by omega
      have hm_le : m₀ ≤ 2 * k := by omega
      have h_step : (m₀ + 2) * (m₀ + 1) ≤ 2 ^ (2 * k + 1) := by
        have h_prod : (m₀ + 2) * (m₀ + 1) ≤ (2 * k + 2) * (2 * k + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        exact h_prod.trans (mul_two_add_le_two_pow hk)
      have h_eq : d + 2 + 7 = m₀ + 2 := by omega
      rw [h_eq, h_k_succ, Nat.factorial_succ (m₀ + 1), Nat.factorial_succ m₀]
      have h_sq : (k + 1) ^ 2 = (2 * k + 1) + k ^ 2 := by ring
      rw [h_sq, Nat.pow_add]
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul h_step ih'

/-- **Lemma 2.1** of Maróti (2002), pages 635–636: for integers `a, b, m` with `8 ≤ m`, `2 ≤ a`,
`2 ≤ b`, and `m = a * b`, `m! ≤ (m! / (b! ^ a * a!)) ^ ⌊log₂ (m! / (b! ^ a * a!))⌋`. -/
theorem lemma_2_1 (a b m : ℕ) (hm : 8 ≤ m) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : m = a * b) :
    m ! ≤ (m ! / (b ! ^ a * a !)) ^ Nat.log 2 (m ! / (b ! ^ a * a !)) := by
  subst hab
  set N := (a * b)! / ((b !) ^ a * a !)
  set k := (a * b + 1) / 2
  have hN : 2 ^ k ≤ N := two_pow_half_le_quotient ha hb hm
  have hk_log : k ≤ Nat.log 2 N := by
    have h2 : 1 < 2 := by decide
    calc k = Nat.log 2 (2 ^ k) := (Nat.log_pow h2 k).symm
      _ ≤ Nat.log 2 N := Nat.log_mono_right hN
  have hN_pos : 1 ≤ N := by
    have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    omega
  calc (a * b)!
    _ ≤ 2 ^ (k ^ 2) := factorial_le_two_pow_sq_half (by omega)
    _ = (2 ^ k) ^ k := by rw [sq, Nat.pow_mul]
    _ ≤ N ^ k := Nat.pow_le_pow_left hN k
    _ ≤ N ^ Nat.log 2 N := Nat.pow_le_pow_right hN_pos hk_log

end Maroti
