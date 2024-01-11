import Coinduction.AlgebraicCompletePartialOrder

#print Monotone

instance (α : Type) [CompletePartialOrder α] : OmegaCompletePartialOrder α := inferInstance

#print OmegaCompletePartialOrder.Continuous

open OmegaCompletePartialOrder (Continuous)
open CompletePartialOrder (IsCompactElement)

structure Haddock {α β : Type*} [AlgebraicCompletePartialOrder β] (f : (α → β) →o (α → β)) where 
  cont : ∀ (g : (WithTop ℕ) → α → β), (∀ a, Continuous (g . a)) → (∀ a, Continuous <| fun n ↦ f (g n) a)
  comp : ∀ (g : α → β), (∀ a, IsCompactElement <| g a) → (∀ a, IsCompactElement <| f g a)








  