import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm <;> apply le_inf <;> first | apply inf_le_left | apply inf_le_right

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm <;> apply le_inf
  any_goals apply le_inf
  any_goals first | apply inf_le_left | apply inf_le_right
  any_goals apply le_trans (inf_le_left : x ⊓ y ⊓ z ≤ x ⊓ y)
  any_goals apply le_trans (inf_le_right  : x ⊓ (y ⊓ z) ≤ y ⊓ z)
  all_goals first | apply inf_le_left | apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm <;> apply sup_le <;> first | apply le_sup_left | apply le_sup_right

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm <;> apply sup_le
  any_goals apply sup_le
  any_goals first | apply le_sup_left | apply le_sup_right
  any_goals refine le_trans ?_ (le_sup_left : x ⊔ y ≤ x ⊔ y ⊔ z)
  any_goals refine le_trans ?_ (le_sup_right : y ⊔ z ≤ x ⊔ (y ⊔ z))
  all_goals first | apply le_sup_left | apply le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  · apply le_inf
    · rfl
    · apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · rfl
    · apply inf_le_left
  · apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  apply le_antisymm
  · apply sup_le <;> apply le_inf
    repeat apply le_sup_left
    · exact le_trans (inf_le_left ..) (le_sup_right ..)
    · exact le_trans (inf_le_right ..) (le_sup_right ..)
  · rw [h]
    apply sup_le
    · rw [inf_comm, absorb1]
      apply le_sup_left
    · rw [inf_comm, h]
      apply sup_le
      · exact le_trans (inf_le_right ..) (le_sup_left ..)
      · rw [inf_comm]
        apply le_sup_right

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  apply le_antisymm
  · rw [h]
    apply le_inf
    · rw [sup_comm _ a, absorb2]
      apply inf_le_left
    · rw [sup_comm (a ⊓ b), h]
      apply le_inf
      · exact le_trans (inf_le_left ..) (le_sup_right ..)
      · rw [sup_comm]
        exact inf_le_right
  · apply le_inf <;> apply sup_le
    repeat apply inf_le_left
    · exact le_trans (inf_le_right ..) (le_sup_left ..)
    · exact le_trans (inf_le_right ..) (le_sup_right ..)

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  rw [← add_neg_cancel a, sub_eq_add_neg]
  apply add_le_add_right h

example (h: 0 ≤ b - a) : a ≤ b := by
  rw [← zero_add a, ← sub_add_cancel b a]
  apply add_le_add_right h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have : 0 ≤ b - a := by
    rw [← add_neg_cancel a, sub_eq_add_neg]
    apply add_le_add_right h
  calc
    a * c = a * c + 0 := (add_zero _).symm
    _ ≤ a * c + (b - a) * c := by
      apply add_le_add_left
      exact mul_nonneg this h'
    _ = b * c := by noncomm_ring

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have := dist_triangle x y x
  rwa [dist_self x, dist_comm y x, nonneg_add_self_iff] at this

end
