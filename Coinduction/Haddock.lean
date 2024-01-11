import Coinduction.AlgebraicCompletePartialOrder 

#print Monotone

instance (α : Type) [CompletePartialOrder α] : OmegaCompletePartialOrder α := inferInstance

#print OmegaCompletePartialOrder.Continuous

#check CompletePartialOrder

open CompletePartialOrder (IsCompactElement)

structure Haddock {α β : Type*} [AlgebraicCompletePartialOrder β] (F : (α → β) → (α → β)) where 
  mono : Monotone F
  cont : ∀ {g : (WithTop ℕ) → α → β}, (∀ a, ScottContinuous (g . a)) → (∀ a, ScottContinuous <| fun n ↦ F (g n) a)
  comp : ∀ {g : α → β}, (∀ a, IsCompactElement <| g a) → (∀ a, IsCompactElement <| F g a)



variable {α : Type*} {β : Type*} [AlgebraicCompletePartialOrder β]
variable (F : (α → β) → (α → β)) (haddock : Haddock F)

#print CompletePartialOrder
#print OrderBot

@[simp]
def withFuel (fuel : ℕ) (a : α) : β := 
  match fuel with 
  | 0      => ⊥
  | fuel' + 1 => F (withFuel fuel') a


lemma with_fuel_comp (fuel : ℕ) (a : α) : IsCompactElement (withFuel F fuel a) := by 
  induction fuel generalizing a with 
  | zero => 
    unfold withFuel
    exact CompletePartialOrder.bot_compact 
  | succ n ih => 
    unfold withFuel 
    exact haddock.comp ih a

lemma with_fuel_succ (a : α) (fuel : ℕ) : 
  (withFuel F fuel a) ≤ withFuel F (fuel + 1) a := by 
  induction fuel generalizing a with 
  | zero => 
    unfold withFuel ; exact bot_le 
  | succ φ ih => 
    apply haddock.mono
    exact ih 
  

lemma with_fuel_mono (a : α) : Monotone (withFuel F . a) := by 
  intros φ φ' h_le 
  dsimp only 
  induction h_le with 
  | refl => apply le_refl 
  | @step m _ ih => 
    have := with_fuel_succ F haddock a m
    exact le_trans ih this



