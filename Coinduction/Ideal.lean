import Mathlib.Order.Ideal

instance {α : Type} [PartialOrder α] : PartialOrder (Order.Ideal α) := inferInstance

variable {α : Type*} [PartialOrder α] [OrderBot α]

-- lemma single_bot_lower : IsLowerSet {(⊥ : α)} := by
--   unfold IsLowerSet
--   intros a b h_le h_mem
--   cases h_mem
--   rw [Set.mem_singleton_iff]
--   exact le_bot_iff.mp h_le

-- lemma single_directed (a : α) : DirectedOn (. ≤ .) {a} := by
--   unfold DirectedOn
--   intros x h_mem_x x' h_mem_x'
--   cases h_mem_x
--   cases h_mem_x'
--   use a
--   simp?

def IdealBot : Order.Ideal α := Order.Ideal.principal ⊥
  -- carrier := {⊥}
  -- lower' := single_bot_lower
  -- nonempty' := @Set.nonempty_of_mem α {⊥} ⊥ rfl
  -- directed' := single_directed _

-- ideals ppo
#synth OrderBot (Order.Ideal α)

#synth PartialOrder (Order.Ideal α)
