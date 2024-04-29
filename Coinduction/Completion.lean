import Coinduction.AlgebraicCompletePartialOrder

namespace AlgebraicCompletePartialOrder

set_option autoImplicit false

#check OrderHom
#check Equiv

#print FunLike

def Bimonotone {α : Type*} [PartialOrder α] {β : Type*} [PartialOrder β] (f : α → β) :=
  ∀ a a', a ≤ a' ↔ f a ≤ f a'

lemma injective_of_bimonotone {α : Type*} [PartialOrder α] {β : Type*} [PartialOrder β] (f : α → β) :
  Bimonotone f → Function.Injective f :=
  fun h_bimono a a' h_eq ↦ le_antisymm ((h_bimono a a').mpr (by rw [h_eq])) ((h_bimono a' a).mpr (by rw [h_eq]))


structure Completion (α : Type*) [PartialOrder α] [OrderBot α] (β : Type*) [AlgebraicCompletePartialOrder β] where
  toFun : α → β
  to_fun_bot : toFun ⊥ = ⊥
  to_fun_bimono : Bimonotone toFun
  to_fun_compact : ∀ a, CompletePartialOrder.IsCompactElement (toFun a)
  invFun : β → α
  compact_inv : ∀ (b : β) (a : α), CompletePartialOrder.IsCompactElement b → (invFun b = a ↔ toFun a = b)

section

  variable {α : Type*} [PartialOrder α] [OrderBot α] {β : Type*} [AlgebraicCompletePartialOrder β]

  #check Function.Injective

  #check OrderIso

  variable (e : Completion α β)

  lemma completion_injective : Function.Injective e.toFun :=
    injective_of_bimonotone e.toFun e.to_fun_bimono

  open CompletePartialOrder (IsCompactElement CompactsLe)

  lemma to_fun_compacts (b : β) : CompletePartialOrder.IsCompactElement b ↔ ∃ a, e.toFun a = b := by
    apply Iff.intro <;> intros h
    . use e.invFun b
      exact e.compact_inv _ (e.invFun b) h |>.mp rfl
    . rcases h with ⟨a, ha⟩
      rw [← ha]
      exact e.to_fun_compact _

  @[simp]
  lemma compact_inv_right {b : β} : IsCompactElement b → e.toFun (e.invFun b) = b :=
    fun h_comp ↦ e.compact_inv _ _ h_comp |>.mp rfl

  @[simp]
  lemma compact_inv_left {a : α} : e.invFun (e.toFun a) = a :=
    e.compact_inv _ _ (e.to_fun_compact _) |>.mpr rfl

  lemma inv_fun_bimonotone (b₁ b₂ : β) :
    IsCompactElement b₁ → IsCompactElement b₂ → (b₁ ≤ b₂ ↔ e.invFun b₁ ≤ e.invFun b₂) := by
    intros h_comp_b₁ h_comp_b₂
    let a₁ := e.invFun b₁ ; have heq₁ : a₁ = e.invFun b₁ := rfl ; -- is there no shortcut for this?
    let a₂ := e.invFun b₂ ; have heq₂ : a₂ = e.invFun b₂ := rfl ;
    rw [e.compact_inv _ _ h_comp_b₁] at heq₁
    rw [e.compact_inv _ _ h_comp_b₂] at heq₂
    rw [← heq₁, ←heq₂]
    apply Iff.intro
    . nth_rw 2 [heq₁, heq₂]
      exact e.to_fun_bimono _ _ |>.mpr
    . nth_rw 1 [heq₁, heq₂]
      exact e.to_fun_bimono _ _ |>.mp



  lemma completion_le (b₁ b₂ : β) :
    b₁ ≤ b₂ ↔ (∀ a₁ ∈ CompactsLe b₁, ∃ a₂ ∈ CompactsLe b₂, a₁ ≤ a₂) := by
    apply Iff.intro
    . intros h_b_le
      rw [AlgebraicCompletePartialOrder.compactly_generated b₁] at h_b_le
      rw [AlgebraicCompletePartialOrder.compactly_generated b₂] at h_b_le
      have := @CompletePartialOrder.forall_exists_le_iff_sSup_le_sSup _ _ (CompactsLe b₁) (CompactsLe b₂) (compacts_le_directed _) (compacts_le_directed _) (CompletePartialOrder.compacts_le_nonempty _) (fun _ ⟨h, _⟩ ↦ h)
      rw [← this] at h_b_le
      intros a ha
      exact h_b_le _ ha
    . intros h
      rw [compactly_generated b₁, compactly_generated b₂]
      have := @CompletePartialOrder.forall_exists_le_iff_sSup_le_sSup _ _ (CompactsLe b₁) (CompactsLe b₂) (compacts_le_directed _) (compacts_le_directed _) (CompletePartialOrder.compacts_le_nonempty _) (fun _ ⟨h, _⟩ ↦ h)
      rw [← this]
      intros a ha
      exact h a ha

end




-- section FunctionLifting
--   open CompletePartialOrder

--   #check MonotoneOn

--   section FLift

--     variable {α β : Type} [AlgebraicCompletePartialOrder α] [AlgebraicCompletePartialOrder β]

--     def flift (f : α → β) : α → β := fun a ↦ sSup (f '' CompactsLe a)

--     lemma flift_directed (f : α → β) (hcomp : ∀ a, IsCompactElement a → IsCompactElement (f a)) (hmono : MonotoneOn f (Compacts α))
--       : ∀ a, DirectedOn (. ≤ .) (f '' CompactsLe a) := by
--       intros a


--   end FLift

--   open Classical in
--   noncomputable def bot_ext {α₁ α₂ : Type} {α₁' α₂' : Type} [PartialOrder α₁] [PartialOrder α₂] [OrderBot α₁] [OrderBot α₂] [AlgebraicCompletePartialOrder α₁'] [AlgebraicCompletePartialOrder α₂'] (e₁ : Completion α₁ α₁') (e₂ : Completion α₂ α₂')
--     (f : α₁ → α₂) : α₁' → α₂' := fun x ↦ if IsCompactElement x then e₂.toFun (f <| e₁.invFun x) else ⊥

--   noncomputable def flift_bot_ext {α₁ α₂ : Type} {α₁' α₂' : Type} [PartialOrder α₁] [PartialOrder α₂] [OrderBot α₁] [OrderBot α₂] [AlgebraicCompletePartialOrder α₁'] [AlgebraicCompletePartialOrder α₂'] (e₁ : Completion α₁ α₁') (e₂ : Completion α₂ α₂')
--     (f : α₁ → α₂) : α₁' → α₂' := flift (bot_ext e₁ e₂ f)

-- end FunctionLifting
