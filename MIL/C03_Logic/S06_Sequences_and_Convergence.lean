import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n nge
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by congr 1; ring
    _ ≤ |s n - a| + |t n - b| := by apply abs_add
    _ < ε / 2 + ε / 2 := by
      apply add_lt_add
      · exact hs n (le_trans (le_max_left ..) nge)
      · exact ht n (le_trans (le_max_right ..) nge)
    _ = ε := by ring

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  set ε' := ε / |c| with ε'def
  have ε'pos : 0 < ε' := div_pos εpos acpos
  rcases cs ε' ε'pos with ⟨N, hN⟩
  use N
  intro n hn
  specialize hN n hn
  calc
    |c * s n - c * a| = |c| * |s n - a| := by
      rw [← mul_sub, abs_mul]
    _ < |c| * ε' := by
      rw [mul_lt_mul_left] <;> assumption
    _ = ε := by
      rw [ε'def]
      exact mul_div_cancel₀ ε (ne_of_gt acpos)

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  specialize h n hn
  calc
    |s n| = |a + (s n - a)| := by rw [add_sub_cancel]
    _ ≤ |a| + |s n - a| := abs_add ..
    _ < |a| + 1 := add_lt_add_left h _

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n hn
  rw [sub_zero, abs_mul]
  calc
    |s n| * |t n| < B * (ε / B) := by
      apply mul_lt_mul''
      · apply h₀
        exact le_trans (le_max_left ..) hn
      · rw [← sub_zero (t n)]
        apply h₁
        exact le_trans (le_max_right ..) hn
      repeat apply abs_nonneg
    _ = ε := by rw [mul_div_cancel₀]; exact ne_of_gt Bpos

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by rwa [gt_iff_lt, abs_sub_pos]
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by apply hNa; apply le_max_left
  have absb : |s N - b| < ε := by apply hNb; apply le_max_right
  have : |a - b| < |a - b| := by calc
    |a - b| = |(s N - b) - (s N - a)| := by congr 1; ring
    _ ≤ |s N - b| + |s N - a| := abs_sub ..
    _ < ε + ε := by apply add_lt_add <;> assumption
    _ = |a - b| := by ring
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
