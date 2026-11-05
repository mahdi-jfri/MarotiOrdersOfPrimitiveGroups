module

public import Maroti.Alternating.Lemma21
public import Maroti.Bound

/-!
# Arithmetic bounds on `Maroti.bound` for the alternating case

This file proves arithmetic inequalities for
`Maroti.bound n = n * ∏ i ∈ Finset.range (Nat.log 2 n), (n - 2 ^ i)` used in Step 3 of Section 2
of A. Maróti, *On the orders of primitive groups*, J. Algebra 258 (2002), pages 633 and 635.

The function `n ↦ n ^ Nat.log 2 n` is monotone on positive natural numbers (`pow_log_mono`).
For `9 ≤ m`, if `((m + 1) / 2)! ≤ 2 * n`, combining `2 * 2 ^ k ≤ k!` for
`k = (m + 1) / 2 ≥ 5` with `factorial_le_two_pow_sq_half` and `pow_log_le_bound` yields
`m! ≤ bound n` (`factorial_le_bound_of_bochert`).
-/

@[expose] public section

namespace Maroti.Alternating

open scoped Nat

/-- For `1 ≤ m ≤ n`, `m ^ Nat.log 2 m ≤ n ^ Nat.log 2 n`. -/
theorem pow_log_mono {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    m ^ Nat.log 2 m ≤ n ^ Nat.log 2 n := by
  calc m ^ Nat.log 2 m
    _ ≤ n ^ Nat.log 2 m := Nat.pow_le_pow_left hmn (Nat.log 2 m)
    _ ≤ n ^ Nat.log 2 n := Nat.pow_le_pow_right (by omega) (Nat.log_mono_right hmn)

/-- For `5 ≤ k`, `2 * 2 ^ k ≤ k !`. -/
private theorem two_mul_two_pow_le_factorial {k : ℕ} (hk : 5 ≤ k) :
    2 * 2 ^ k ≤ k ! := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 5 := ⟨k - 5, by omega⟩
  induction d with
  | zero => decide
  | succ d ih =>
    have ih' := ih (by omega)
    rw [Nat.factorial_succ]
    calc 2 * 2 ^ (d + 1 + 5)
      _ = 2 * (2 * 2 ^ (d + 5)) := by
        have : d + 1 + 5 = (d + 5) + 1 := by omega
        rw [this, Nat.pow_succ]
        ring
      _ ≤ (d + 1 + 5) * (d + 5)! := Nat.mul_le_mul (by omega) ih'

/-- For `9 ≤ m`, if `((m + 1) / 2)! ≤ 2 * n`, then `m ! ≤ bound n`. -/
theorem factorial_le_bound_of_bochert {m n : ℕ} (hm : 9 ≤ m)
    (hn : ((m + 1) / 2)! ≤ 2 * n) : m ! ≤ bound n := by
  set k := (m + 1) / 2
  have hk : 5 ≤ k := by omega
  have h2k : 2 * 2 ^ k ≤ k ! := two_mul_two_pow_le_factorial hk
  have hpow_le : 2 ^ k ≤ n := by omega
  have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
  have hn_pos : 1 ≤ n := by omega
  have hk_log : k ≤ Nat.log 2 n := by
    calc k = Nat.log 2 (2 ^ k) := (Nat.log_pow (by decide) k).symm
      _ ≤ Nat.log 2 n := Nat.log_mono_right hpow_le
  calc (m !)
    _ ≤ 2 ^ (k ^ 2) := factorial_le_two_pow_sq_half (by omega)
    _ = (2 ^ k) ^ k := by rw [sq, Nat.pow_mul]
    _ ≤ n ^ k := Nat.pow_le_pow_left hpow_le k
    _ ≤ n ^ Nat.log 2 n := Nat.pow_le_pow_right hn_pos hk_log
    _ ≤ bound n := pow_log_le_bound hn_pos

end Maroti.Alternating
