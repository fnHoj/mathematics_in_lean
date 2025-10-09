import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with nnx | negx
  · rw [abs_of_nonneg nnx]
  · rw [abs_of_neg negx]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rw [← abs_neg]
  exact le_abs_self (-x)

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with hxy | hxy
  · rw [abs_of_nonneg hxy]
    apply add_le_add <;> apply le_abs_self
  · rw [abs_of_neg hxy, neg_add]
    apply add_le_add <;> apply neg_le_abs_self

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · intro hx
    rcases le_or_gt 0 y with nny | negy
    · rw [abs_of_nonneg nny] at hx
      exact Or.inl hx
    · rw [abs_of_neg negy] at hx
      exact Or.inr hx
  · rintro (xlt | xlt)
    · exact lt_of_lt_of_le xlt (le_abs_self y)
    · exact lt_of_lt_of_le xlt (neg_le_abs_self y)

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with hx | hx
  rw [abs_of_nonneg hx]
  swap; rw [abs_of_neg hx]
  all_goals constructor <;> first
  | (rintro ⟨_, _⟩; linarith)
  | (intro; constructor <;> linarith)

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left; exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩
  repeat linarith [pow_two_nonneg x, pow_two_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  replace h : (x - 1) * (x + 1) = 0 := by calc
    (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
    _ = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h with hx | hx
  · left; linarith
  · right; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  replace h : (x - y) * (x + y) = 0 := by calc
    (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
    _ = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h with hx | hx
  · left; linarith
  · right; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  replace h : (x - 1) * (x + 1) = 0 := by calc
    (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
    _ = 0 := by rw [h]; norm_num
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h with hx | hx
  · left; rw [← sub_add_cancel x 1, hx]; norm_num
  · right; rw [← add_sub_cancel_right x 1, hx]; norm_num

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  replace h : (x - y) * (x + y) = 0 := by calc
    (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
    _ = 0 := by rw [h]; norm_num
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h with hx | hx
  · left; rw [← sub_add_cancel x y, hx]; norm_num
  · right; rw [← add_sub_cancel_right x y, hx]; norm_num

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro ptoq
    by_cases h : P
    · exact Or.inr (ptoq h)
    · exact Or.inl h
  · rintro (np | q) p
    · contradiction
    · assumption
