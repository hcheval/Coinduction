import Coinduction.CompletePartialOrder



#check OmegaCompletePartialOrder
open CompletePartialOrder (IsCompactElement CompactsLe)

class AlgebraicCompletePartialOrder (α : Type*) extends CompletePartialOrder α, OrderBot α where
  compactly_generated : ∀ a : α, a = sSup (CompactsLe a)
  compacts_le_directed : ∀ a : α, DirectedOn (. ≤ .) (CompactsLe a)

variable {α β : Type*} [AlgebraicCompletePartialOrder α] [AlgebraicCompletePartialOrder β]

-- def IsεδContinuous (f : α → β) : Prop :=
--   ∀ a : α, ∀ ε : β, IsCompactElement ε → ε ≤ f a → ∃ δ : α, IsCompactElement δ ∧ δ ≤ a ∧ ε ≤ f δ
