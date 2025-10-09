import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · exact ⟨xs, Or.inl xt⟩
  · exact ⟨xs, Or.inr xu⟩

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  repeat constructor
  · exact xs
  all_goals (intro; apply xntu; tauto)

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun _x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm (λ _x ⟨xs, xt⟩ ↦ ⟨xt, xs⟩) (λ _x ⟨xt, xs⟩ ↦ ⟨xs, xt⟩)
example : s ∩ (s ∪ t) = s := by
  ext x; constructor
  · rintro ⟨xs, - | -⟩ <;> assumption
  · intro xs
    exact ⟨xs, Or.inl xs⟩

example : s ∪ s ∩ t = s := by
  ext x; constructor
  · rintro (xs | ⟨xs, -⟩) <;> assumption
  · exact Or.inl

example : s \ t ∪ t = s ∪ t := by
  ext x; constructor
  · rintro (⟨xs, -⟩ | xt)
    left; assumption
    right; assumption
  · rintro (xs | xt)
    · by_cases xt : x ∈ t
      · right; assumption
      · left; constructor <;> assumption
    · right; assumption

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x; constructor
  · rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    · use Or.inl xs
      rintro ⟨-, xt⟩; contradiction
    · use Or.inr xt
      rintro ⟨xs, -⟩; contradiction
  · rintro ⟨xs | xt, xnst⟩
    · left; use xs
      intro xt
      apply xnst; constructor <;> assumption
    · right; use xt
      intro xs
      apply xnst; constructor <;> assumption

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  simp
  intro nprime ngt
  exact Nat.Prime.odd_of_ne_two nprime (ne_of_gt ngt)

#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  specialize ssubt xs
  constructor
  · apply h₀; assumption
  · apply h₁; assumption

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, xs, -, prime_x⟩
  use x, ssubt xs

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  constructor
  · rintro (xs | hx) _ ⟨i, rfl⟩
    · right; assumption
    · left; apply hx; use i
  · intro hx
    by_cases xs : x ∈ s
    · left; assumption
    · right
      rintro _ ⟨i, rfl⟩
      specialize hx (A i ∪ s) ⟨i, rfl⟩
      exact Or.resolve_right hx xs

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  rw [eq_univ_iff_forall]
  intro x
  rw [mem_iUnion₂]
  rcases Nat.exists_infinite_primes x with ⟨p, pgex, prime_p⟩
  use p, prime_p, pgex

end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
