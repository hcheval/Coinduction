import Mathlib.Order.CompletePartialOrder



namespace DirectedOn

  variable {α : Type*} [CompletePartialOrder α]

  theorem IsLUB.sSup_eq {s : Set α} (hs : DirectedOn (. ≤ .) s) (h : IsLUB s a) : sSup s = a :=
      (DirectedOn.isLUB_sSup hs).unique h

  example {s : Set α} : DirectedOn (. ≤ .) s → b ∈ s → a ≤ b → a ≤ sSup s :=
    fun h_dir h_mem h_le ↦ le_trans h_le (DirectedOn.le_sSup h_dir h_mem)

  theorem sSup_le_sSup {s t : Set α} (h : s ⊆ t) (hs : DirectedOn (. ≤ . ) s) (ht : DirectedOn (. ≤ .) t): sSup s ≤ sSup t :=
    (DirectedOn.isLUB_sSup hs).mono (DirectedOn.isLUB_sSup ht) h

  @[simp]
  theorem sSup_le_iff {s : Set α} (hs : DirectedOn (. ≤ .) s): sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
    isLUB_le_iff (DirectedOn.isLUB_sSup hs)

  theorem le_sSup_iff {s : Set α} (hs : DirectedOn (. ≤ .) s): a ≤ sSup s ↔ ∀ b ∈ upperBounds s, a ≤ b :=
    ⟨fun h _ hb => le_trans h (DirectedOn.sSup_le hs hb), fun hb => hb _ fun _ => DirectedOn.le_sSup hs⟩

  theorem sSup_le_sSup_of_forall_exists_le {s t : Set α} (hs : DirectedOn (. ≤ .) s) (ht : DirectedOn (. ≤ .) t)
    (h : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) : sSup s ≤ sSup t :=
    (le_sSup_iff ht).2 fun _ hb =>
      DirectedOn.sSup_le hs fun a ha =>
        let ⟨_, hct, hac⟩ := h a ha
        hac.trans (hb hct)

end DirectedOn

namespace CompletePartialOrder

  variable {α : Type*} [CompletePartialOrder α]

  def IsCompactElement (a : α) : Prop :=
    ∀ d : Set α, DirectedOn (. ≤ .) d → d.Nonempty → a ≤ sSup d → ∃ a' ∈ d, a ≤ a'

  def Compacts (α : Type*) [CompletePartialOrder α] := {a : α // IsCompactElement a}

  def CompactsLe (a : α) : Set α :=
    {a' : α | IsCompactElement a' ∧ a' ≤ a}

  variable [OrderBot α]

  lemma bot_compact : IsCompactElement (⊥ : α) := by
    intros d h_dir h_nonempty h_bot_le
    let a := Nonempty.some <| Set.nonempty_coe_sort.mpr h_nonempty
    use a
    exact ⟨a.2, bot_le⟩

  lemma compacts_le_nonempty (a : α) : CompactsLe a |>.Nonempty :=
    ⟨⊥, ⟨bot_compact, bot_le⟩⟩

  -- lemma compacts_le_directed (a : α) : DirectedOn (. ≤ .) (CompactsLe a) := by


-- #check CompleteSemilatticeSup.le_sSup
-- theorem le_sSup : a ∈ s → a ≤ sSup s :=
--   CompleteSemilatticeSup.le_sSup s a
-- #align le_Sup le_sSup


-- theorem isLUB_sSup (s : Set α) : IsLUB s (sSup s) :=
--   ⟨fun _ ↦ le_sSup, fun _ ↦ sSup_le⟩
-- #align is_lub_Sup isLUB_sSup



  lemma forall_exists_le_iff_sSup_le_sSup {d₁ d₂ : Set α} :
    DirectedOn (. ≤ .) d₁ → DirectedOn (. ≤ .) d₂ → d₂.Nonempty → (∀ a₁ ∈ d₁, IsCompactElement a₁) →
    ((∀ a₁ ∈ d₁, ∃ a₂ ∈ d₂, a₁ ≤ a₂) ↔ sSup d₁ ≤ sSup d₂) := by
    intros h_dir₁ h_dir₂ h_ne_d₂ h_comp_a₁
    apply Iff.intro
    . intros h
      have := DirectedOn.sSup_le_sSup_of_forall_exists_le h_dir₁ h_dir₂ h
      exact this
    . intros h a₁ h_mem_a₁
      specialize h_comp_a₁ a₁ h_mem_a₁
      have : a₁ ≤ sSup d₂ := le_trans (DirectedOn.le_sSup h_dir₁ h_mem_a₁) h
      exact h_comp_a₁ d₂ h_dir₂ h_ne_d₂ this

end CompletePartialOrder

def Carrier {α : Type} {β : α → Type} [∀ a, Bot (β a)] (f : ∀ a, β a):=
  {a | f a ≠ ⊥}


section Pi

variable {ι : Type} {α : ι → Type} [∀ i, CompletePartialOrder (α i)]

def proj (s : Set (∀ i, α i)) (i : ι) : Set (α i) :=
  {f i | f ∈ s}

infix:60 " ⇓ " => proj

variable {s : Set <| ∀ i, α i} (hs_ne : s.Nonempty) (hs_dir : DirectedOn (. ≤ .) s)

def proj_extend (j : ι) (a : α j) (h_mem : a ∈ (s ⇓ j)) :
  ∃ f : ∀ i, α i, f ∈ s ∧ f j = a := by
  rcases h_mem with ⟨w, hw⟩
  use w


example (i : ι) : (s ⇓ i).Nonempty := by
  simp only [Set.Nonempty]
  use (hs_ne.some i), hs_ne.some
  exact ⟨hs_ne.some_mem, rfl⟩

example (i : ι) : DirectedOn (. ≤ .) (s ⇓ i) := by
  intros a₁ h_mem₁ a₂ h_mem₂
  let ⟨a₁', h₁'⟩ := (proj_extend _ _ h_mem₁)
  let ⟨a₂', h₂'⟩ := proj_extend _ _ h_mem₂
  specialize hs_dir a₁' h₁'.1 a₂' h₂'.1
  rcases hs_dir with ⟨a'', ⟨h_mem'', h_le₁, h_le₂⟩⟩
  use a'' i
  refine ⟨?_, ?_, ?_⟩
  . use a''
  . aesop
  . aesop



#check DirectedOn.sSup_le
instance : CompletePartialOrder (∀i, α i) where
  lubOfDirected := fun d h_dir => by
    unfold IsLUB IsLeast upperBounds
    constructor
    . intros f h_mem i
      apply DirectedOn.le_sSup
      .




end Pi
