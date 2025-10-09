import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    apply h
    use x
  · rintro h _ ⟨x, xs, rfl⟩
    exact h xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨x', xs, hx⟩
  rwa [h hx] at xs

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro _ ⟨x, hx, rfl⟩
  exact hx

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, rfl⟩
  use x, yu

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro _ ⟨x, xs, rfl⟩
  use x, h xs

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x hx
  exact h hx

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := rfl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro _ ⟨x, ⟨xs, xt⟩, rfl⟩
  constructor <;> use x

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x, xs, rfl⟩, ⟨x', xt, hx'⟩⟩
  rw [h hx'] at xt
  use x, ⟨xs, xt⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro _ ⟨⟨x, xs, rfl⟩, hx⟩
  refine ⟨x, ⟨xs, ?_⟩, rfl⟩
  intro xt
  apply hx
  use x

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := λ _ ↦ id

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext; constructor
  · rintro ⟨⟨x, xs, rfl⟩, fxv⟩
    use x, ⟨xs, fxv⟩
  · rintro ⟨x, ⟨xs, fxv⟩, rfl⟩
    use (by use x), fxv

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro _ ⟨x, ⟨xs, fxu⟩, rfl⟩
  use (by use x), fxu

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, fxu⟩
  use (by use x), fxu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  · left; use x
  · right; assumption

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext; constructor
  · rintro ⟨x, ⟨_, ⟨i, rfl⟩, hx⟩, rfl⟩
    rw [mem_iUnion]
    use i, x
  · rintro ⟨_, ⟨i, rfl⟩, ⟨x, xAi, rfl⟩⟩
    use x; refine ⟨?_, rfl⟩
    rw [mem_iUnion]
    use i

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨i, rfl⟩
  use x, hx (A i) (by use i)

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y hy
  rcases hy (f '' A i) (by use i) with ⟨x, xAi, rfl⟩
  refine ⟨x, ?_, rfl⟩
  rintro _ ⟨j, rfl⟩
  rcases hy (f '' A j) (by use j) with ⟨x', xAj, hx⟩
  rwa [injf hx] at xAj

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x; constructor
  · rintro ⟨_, ⟨i, rfl⟩, fxBi⟩
    rw [mem_iUnion]
    use i, fxBi
  · rintro ⟨_, ⟨i, rfl⟩, fxBi⟩
    change f x ∈ ⋃ i, B i
    rw [mem_iUnion]
    use i, fxBi

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x; constructor
  · rintro hfx _ ⟨i, rfl⟩
    exact hfx (B i) (by use i)
  · rintro hx _ ⟨i, rfl⟩
    exact hx (f ⁻¹' B i) (by use i)

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x nnx y nny h
  calc
    x = √x ^ 2 := by rw [sq_sqrt nnx]
    _ = √y ^ 2 := by rw [h]
    _ = y := by rw [sq_sqrt nny]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x nnx y nny h
  dsimp at h
  calc
    x = √(x ^ 2) := by rw [sqrt_sq nnx]
    _ = √(y ^ 2) := by rw [h]
    _ = y := by rw [sqrt_sq nny]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; constructor
  · rintro ⟨x, nnx, rfl⟩
    apply sqrt_nonneg
  · intro nny
    use y ^ 2, pow_two_nonneg y, sqrt_sq nny

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    dsimp
    apply pow_two_nonneg
  · intro nny
    use √y
    apply sq_sqrt nny

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro injf x
    apply injf
    rw [inverse, dif_pos (by use x)]
    apply choose_spec (p := (f · = f x))
  · intro hinv x y hxy
    rw [← hinv x, ← hinv y, hxy]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro surjf y
    rcases surjf y with ⟨x, rfl⟩
    rw [inverse, dif_pos (by use x)]
    apply choose_spec (p := (f · = f x))
  · intro hinv y
    use inverse f y, hinv y

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := h ▸ h₁
  contradiction

-- COMMENTS: TODO: improve this
end
