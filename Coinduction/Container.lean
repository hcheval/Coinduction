
import Coinduction.CompletePartialOrder
import Coinduction.Embedding
import Mathlib.Order.CompletePartialOrder
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false

inductive Container {α : Type} (β : α → Type) where
| bottom : Container β
| node (a : α) (f : β a → Container β) : Container β

variable {α : Type} {β : α → Type}

lemma eq_node {a : α} {f f' : β a → Container β} : Container.node a f = Container.node a f' ↔ f = f' := by
  constructor
  . intros h ; cases h ; rfl
  . intros h ; rw [h]


inductive WellFormedContainer {α : Type} {β : α → Type} : Container β → Type
| bottom : WellFormedContainer .bottom
| node (a : α) (f : β a → Container β) :
  (∀ b, WellFormedContainer (f b)) → Fintype {a // f a ≠ Container.bottom} → WellFormedContainer (.node a f)


abbrev FiniteContainer {α : Type} (β : α → Type) := {c : Container β // Nonempty <| WellFormedContainer c}


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

instance : Bot (FiniteContainer β) where
  bot := ⟨.bottom, ⟨.bottom⟩⟩

theorem eq_of_definition_order {a₁ a₂ : α} {f₁ : β a₁ → Container β} {f₂ : β a₂ → Container β} :
  DefinitionOrder (.node a₁ f₁) (.node a₂ f₂) → a₁ = a₂ := by
  intros h ; cases h ; rfl


theorem WellFormedContainer.le_refl {c : Container β} (wf : WellFormedContainer c) :
  DefinitionOrder c c := by
  induction wf with
  | bottom =>
    apply DefinitionOrder.bot_le
  | node a f h h' ih =>
    constructor
    exact ih


theorem WellFormedContainer.le_trans
  {c₁ c₂ c₃ : Container β}
  (wf₁ : WellFormedContainer c₁) (wf₂ : WellFormedContainer c₂) (wf₃ : WellFormedContainer c₃)
  : DefinitionOrder c₁ c₂ → DefinitionOrder c₂ c₃ → DefinitionOrder c₁ c₃ :=
  match wf₁, wf₂, wf₃ with
  | .bottom, _, _ => fun _ _ => .bot_le
  | .node a₁ f₁ h₁' h₁, .bottom, c₃ => by intros h h' ; cases h' ; cases h
  | _, _, .bottom => fun h h' => by cases h' ; cases h ; constructor
  | .node a₁ f₁ h₁' h₁, .node a₂ f₂ h₂' h₂, .node a₃ f₃ h₃' h₃ => by
    intros h h'
    have := eq_of_definition_order h
    subst this
    have := eq_of_definition_order h'
    subst this
    cases h with | @node_le _ _ _ h =>
    cases h' with | @node_le _ _ _ h' =>
    constructor
    intros b
    specialize h b
    specialize h' b
    exact WellFormedContainer.le_trans (h₁' b) (h₂' b) (h₃' b) h h'
  -- | _, _, _ => sorry

theorem WellFormedContainer.le_antisymm
  {c₁ c₂ : Container β}
  (wf₁ : WellFormedContainer c₁) (wf₂ : WellFormedContainer c₂) :
  DefinitionOrder c₁ c₂ → DefinitionOrder c₂ c₁ → c₁ = c₂ :=
  match wf₁, wf₂ with
  | .node a₁ f₁ h₁ h₁', .node a₂ f₂ h₂ h₂' => by
    intros h h'
    have := eq_of_definition_order h
    subst this
    cases h with | node_le h =>
    cases h' with | node_le h' =>
    apply eq_node.2
    ext b
    exact WellFormedContainer.le_antisymm (h₁ b) (h₂ b) (h b) (h' b)
  | _, .bottom => by
    intros h h'
    cases h ; rfl
  | .bottom, _ => by
    intros h h'
    cases h' ; rfl

theorem FiniteContainer.le_refl {c : FiniteContainer β} :
  FiniteContainer.DefinitionOrder c c :=
  WellFormedContainer.le_refl c.2.some

theorem FiniteContainer.le_antisymm
  {c₁ c₂ : FiniteContainer β} : FiniteContainer.DefinitionOrder c₁ c₂ → FiniteContainer.DefinitionOrder c₂ c₁ → c₁ = c₂ :=
  fun h h' => by
    let wf₁ := c₁.2.some
    let wf₂ := c₂.2.some
    have := WellFormedContainer.le_antisymm wf₁ wf₂ h h'
    ext
    exact this


theorem FiniteContainer.le_trans
  {c₁ c₂ c₃ : FiniteContainer β} : FiniteContainer.DefinitionOrder c₁ c₂ → FiniteContainer.DefinitionOrder c₂ c₃ → FiniteContainer.DefinitionOrder c₁ c₃ :=
  fun h h' => WellFormedContainer.le_trans (c₁.2.some) (c₂.2.some) (c₃.2.some) h h'


instance : PartialOrder (FiniteContainer β) where
  le := FiniteContainer.DefinitionOrder
  le_refl := fun _ => FiniteContainer.le_refl
  le_antisymm := fun _ _ h h' => FiniteContainer.le_antisymm h h'
  le_trans := fun _ _ _ h h' => FiniteContainer.le_trans h h'





    -- match c₁, c₂, c₃ with
    -- | .bottom, _, _ => fun _ _ => .bot_le
    -- | .node a₁ f₁, .bottom, c₃ => by intros h h' ; cases h' <;> cases h
    -- | .node a₁ f₁, .node a₂ f₂, .node a₃ f₃ => by
    --   intros h h'
    --   have := eq_of_definition_order h
    --   subst this
    --   have := eq_of_definition_order h'
    --   subst this
    --   cases h with | @node_le _ _ _ h =>
    --   cases h'
    --   constructor




theorem FiniteContainer.bot_le {c : FiniteContainer β} :
  ⊥ ≤ c := @_root_.DefinitionOrder.bot_le _ _ _

instance : OrderBot (FiniteContainer β) where
  bot_le := fun _ => FiniteContainer.bot_le

abbrev FiniteConstructor (β : α → Type) (a : α) := {f : β a → FiniteContainer β // Finite {a // f a ≠ ⊥}}

variable {a : α}


instance {a : α} : Bot (FiniteConstructor β a) where
  bot := ⟨fun _ => ⊥, sorry⟩

instance : OrderBot (FiniteConstructor β a) where
  bot_le := fun f b => FiniteContainer.bot_le


def node' (a : α) (f : FiniteConstructor β a) : FiniteContainer β :=
  ⟨.node a (fun b => (f.1 b).1), ⟨.node a (fun b => (f.1 b).1) (fun b => (f.1 b).2.some) sorry⟩⟩

theorem node'_mono : Monotone (node' a (β := β)) :=
  fun f₁ f₂ hle => DefinitionOrder.node_le hle




variable (C : Type) [AlgebraicCompletePartialOrder C] (Comp : AlgebraicCompletePartialOrder.Embedding (FiniteContainer β) C)

abbrev Constructor (β : α → Type) (a : α) := β a → C

instance : OrderBot (Constructor C β a) := inferInstance

instance : CompletePartialOrder (Constructor C β a) := sorry

instance : AlgebraicCompletePartialOrder (Constructor C β a) := sorry

example : CompletePartialOrder.Compacts (C)
