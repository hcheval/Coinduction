
import Coinduction.CompletePartialOrder
import Coinduction.Completion
import Mathlib.Order.CompletePartialOrder
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Finite

set_option autoImplicit false

inductive Container {α : Type} (β : α → Type) where
| bottom : Container β
| node (a : α) (f : β a → Container β) : Container β

variable {α : Type} {β : α → Type}

lemma eq_node {a : α} {f f' : β a → Container β} : Container.node a f = Container.node a f' ↔ f = f' := by
  constructor
  . intros h ; cases h ; rfl
  . intros h ; rw [h]


inductive WellFormedContainer {α : Type} {β : α → Type} : Container β → Prop where
| bottom : WellFormedContainer .bottom
| node (a : α) (f : β a → Container β) :
  (∀ b, WellFormedContainer (f b)) → Set.Finite {a | f a ≠ Container.bottom} → WellFormedContainer (.node a f)


abbrev FiniteContainer {α : Type} (β : α → Type) := {c : Container β // WellFormedContainer c}


instance : Bot (Container β) where
  bot := Container.bottom

-- def WellFormedContainer.depth (c : Container β) (wf : WellFormedContainer c) : ℕ :=
--   match wf with
--   | .bottom => 0
--   | .node a f wf' hfin => _

def Container.Stream (α : Type) := @Container α (fun _ => Unit)

def Container.ofList : List α → Container.Stream α
  | [] => .bottom
  | x :: xs => .node x (fun _ => Container.ofList xs)

def Container.toList : Container.Stream α → List α
  | .bottom => []
  | .node a f => a :: (Container.toList <| f .unit)

example (l : List α) : Container.toList (Container.ofList l) = l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simpa [Container.ofList, Container.toList]

example (c : Container.Stream α) : Container.ofList (Container.toList c) = c := by
  induction c with
  | bottom => rfl
  | node a f ih =>
    specialize ih ()
    simp_all [Container.toList, Container.ofList]


inductive Rose (α : Type) where
| empty : Rose α
| tree (n : ℕ) : α → (Fin n → Rose α) → Rose α

def Container.Rose (α : Type) := @Container (ℕ × α) (fun (n, a) ↦ Fin n)

def Container.ofRose : _root_.Rose α → Container.Rose α
  | .empty => .bottom
  | .tree n a f => .node (n, a) (fun i => Container.ofRose (f i))

def Container.toRose : Container.Rose α → _root_.Rose α
  | .bottom => .empty
  | .node n f => .tree n.1 n.2 (fun i => Container.toRose (f i))

example (r : Rose α) : Container.toRose (Container.ofRose r) = r := by
  induction r with
  | empty => rfl
  | tree n a t =>
    simp_all [Container.toRose, Container.ofRose]

example (c : Container.Rose α) : Container.ofRose (Container.toRose c) = c := by
  induction c with
  | bottom => rfl
  | node n f =>
    simp_all [Container.toRose, Container.ofRose]

-- inductive T where
-- | empty : T
-- | tree₁ : T → T
-- | tree₂ : T → T

-- def Container.T := @Container Bool (fun _ => Unit)

-- def Container.ofT : _root_.T → Container.T
--   | .empty => .bottom
--   | .tree₁ t => .node false (fun _ => Container.ofT t)
--   | .tree₂ t => .node true (fun _ => Container.ofT t)

-- def Container.toT : Container.T → _root_.T
--   | .bottom => .empty
--   | .node a f => match a with
--     | false => .tree₁ (Container.toT <| f .unit)
--     | true => .tree₂ (Container.toT <| f .unit)



open Container


inductive DefinitionOrder : Container β → Container β → Prop where
| bot_le : ∀ {c}, DefinitionOrder ⊥ c
| node_le {a : α} {f f' : β a → Container β} : (∀ b, DefinitionOrder (f b) (f' b)) → DefinitionOrder (node a f) (node a f')

def FiniteContainer.DefinitionOrder : FiniteContainer β → FiniteContainer β → Prop :=
  fun c₁ c₂ => _root_.DefinitionOrder c₁.val c₂.val

instance Container.instBot : Bot (FiniteContainer β) where
  bot := ⟨.bottom, .bottom⟩

theorem eq_of_definition_order {a₁ a₂ : α} {f₁ : β a₁ → Container β} {f₂ : β a₂ → Container β} :
  DefinitionOrder (.node a₁ f₁) (.node a₂ f₂) → a₁ = a₂ := by
  intros h ; cases h ; rfl


theorem Container.le_refl {c : Container β} :
  DefinitionOrder c c := by
  induction c with
  | bottom =>
    constructor
  | node a f ih =>
    constructor
    exact ih

theorem Container.le_antisymm (c₁ c₂ : Container β) :
  DefinitionOrder c₁ c₂ → DefinitionOrder c₂ c₁ → c₁ = c₂ := by
  intros h₁₂
  induction h₁₂ with
  | bot_le =>
    intros h₂₁
    cases h₂₁
    rfl
  | @node_le a f f' h ih =>
    intros h₂₁
    rcases h₂₁ with h₂₁
    cases h₂₁ with | node_le h₂₁ =>
    congr
    ext b
    exact ih _ (h₂₁ b)

theorem Container.le_trans (c₁ c₂ c₃ : Container β) :
  DefinitionOrder c₁ c₂ → DefinitionOrder c₂ c₃ → DefinitionOrder c₁ c₃ := by
  intros h₁₂
  induction h₁₂ generalizing c₃ with
  | bot_le =>
    intros ; constructor
  | @node_le a f f' h ih =>
    intros h₂₃
    cases h₂₃
    rename_i f'' h₂₃
    constructor
    intros b
    exact ih _ _ (h₂₃ b)


instance Container.partialOrder : PartialOrder (Container β) where
  le := DefinitionOrder
  le_refl := fun _ => Container.le_refl
  le_antisymm := fun _ _ h h' => Container.le_antisymm _ _ h h'
  le_trans := fun _ _ _ h h' => Container.le_trans _ _ _ h h'

theorem FiniteContainer.bot_le {c : FiniteContainer β} :
  ⊥ ≤ c := @DefinitionOrder.bot_le _ _ _

instance : OrderBot (FiniteContainer β) where
  bot_le := fun _ => FiniteContainer.bot_le

-- Fₐᵒ
abbrev FiniteConstructor (β : α → Type) (a : α) :=
  {f : β a → FiniteContainer β // Set.Finite (support f)}

variable {a : α}

instance {a : α} : Bot (FiniteConstructor β a) where
  bot := ⟨fun _ => ⊥, by simp [support]⟩

instance : OrderBot (FiniteConstructor β a) where
  bot_le := fun f b => FiniteContainer.bot_le

example {f g : FiniteConstructor β a} : f ≤ g ↔ f.1 ≤ g.1 := by
  simp_all only [ne_eq, Subtype.coe_le_coe]

example {f g : FiniteConstructor β a} : f ≤ g ↔ ∀ b, f.1 b ≤ g.1 b := by
  aesop?

theorem FiniteContainer.coe_injective (c₁ c₂ : FiniteContainer β) : c₁ ≠ c₂ ↔ (↑c₁ : Container β) ≠ ↑c₂ := by
  constructor
  . aesop?
  . aesop?

-- nodeₐᵒ  : Fₐᵒ → Cᵒ
def node₀ (a : α) : FiniteConstructor β a → FiniteContainer β :=
  fun f => ⟨
    .node a (fun b => (f.1 b).1),
    by
      constructor
      . intros b
        exact f.1 b |>.2
      . have := f.2
        have : (⊥ : FiniteContainer β).val = Container.bottom := rfl
        rw [← this]
        simp_rw [← FiniteContainer.coe_injective]
        assumption
  ⟩

theorem node₀_mono : Monotone (node₀ a (β := β)) :=
  fun _ _ hle => DefinitionOrder.node_le hle

variable (C : Type) [AlgebraicCompletePartialOrder C] (Comp : AlgebraicCompletePartialOrder.Completion (FiniteContainer β) C)

abbrev Constructor (β : α → Type) (a : α) := β a → C

instance : OrderBot (Constructor C β a) := inferInstance

instance : CompletePartialOrder (Constructor C β a) := inferInstance

#synth CompletePartialOrder (Constructor C β a)

#synth AlgebraicCompletePartialOrder (Constructor C β a)
