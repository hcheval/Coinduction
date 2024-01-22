import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Set.Finite



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


  -- Lemma 2.1 from the paper
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

  lemma bot_mem_compacts_le (a : α) : ⊥ ∈ CompactsLe a := ⟨bot_compact, bot_le⟩

  lemma compacts_le_nonempty (a : α) : CompactsLe a |>.Nonempty :=
    ⟨⊥, ⟨bot_compact, bot_le⟩⟩

  lemma compact_iff_compact_on_lower_set (a : α) :
    IsCompactElement a
    ↔
    ∀ d : Set α, DirectedOn (. ≤ .) d → d.Nonempty → IsLowerSet d → a ≤ sSup d → ∃ a' ∈ d, a ≤ a' :=
  by sorry

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

def support {α : Type} {β : α → Type} [∀ a, Bot (β a)] (f : ∀ a, β a):=
  {a | f a ≠ ⊥}

def IsRestrictionOnSupport {α β : Type} [Bot β] (f g : α → β) : Prop :=
  support f ⊆ support g ∧
  ∀ a ∈ support f, f a = g a

def finiteRestrictions {α β : Type} [Bot β] (g : α → β) : Set (α → β) :=
  {f | Set.Finite (support f) ∧ IsRestrictionOnSupport f g}

section Pi

variable {ι : Type} {α : ι → Type} [∀ i, CompletePartialOrder (α i)]

def proj (s : Set (∀ i, α i)) (i : ι) : Set (α i) :=
  {f i | f ∈ s}

infix:60 " ⇓ " => proj

section variable {s : Set <| ∀ i, α i} (hs_ne : s.Nonempty) (hs_dir : DirectedOn (. ≤ .) s)

  def proj_extend (j : ι) (a : α j) (h_mem : a ∈ (s ⇓ j)) :
    ∃ f : ∀ i, α i, f ∈ s ∧ f j = a := by
    rcases h_mem with ⟨w, hw⟩
    use w


  lemma proj_ne (i : ι) : (s ⇓ i).Nonempty := by
    simp only [Set.Nonempty]
    use (hs_ne.some i), hs_ne.some
    exact ⟨hs_ne.some_mem, rfl⟩

  lemma proj_directed (i : ι) : DirectedOn (. ≤ .) (s ⇓ i) := by
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

  lemma proj_is_lub : IsLUB s (fun i ↦ sSup (s ⇓ i)) := by
    constructor <;> intros f hfmem i
    . apply DirectedOn.le_sSup (proj_directed hs_dir i)
      use f
    . dsimp only
      rw [DirectedOn.sSup_le_iff <| proj_directed hs_dir i]
      intros a hamem
      rcases hamem with ⟨g, hgmem, hgeq⟩
      subst hgeq
      dsimp [upperBounds]  at hfmem
      specialize hfmem hgmem
      exact hfmem i

  instance (priority := high) Coinduction.Pi.supSet : SupSet (∀ i, α i) where
    sSup s i := sSup <| s ⇓ i

  instance (priority := high) Coinduction.Pi.completePartialOrder : CompletePartialOrder (∀ i, α i) where
    lubOfDirected := fun _ hs_dir ↦ proj_is_lub hs_dir

  lemma proj_eq_sSup : (fun i ↦ sSup (s ⇓ i)) = sSup s := by
    apply Eq.symm
    exact DirectedOn.IsLUB.sSup_eq hs_dir (proj_is_lub hs_dir)

end

section Lemma16
  variable (s : (i : ι) → Set (α i))
  local notation "S" => Set.pi (@Set.univ ι) s

-- Lemma 16.(i)
lemma Pi.directed (hs_dir : ∀ i, DirectedOn (. ≤ .) (s i)) :
  DirectedOn (. ≤ .) (Set.pi (@Set.univ ι) s) := by
  intros a h_mem_a b h_mem_b
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left] at h_mem_a h_mem_b
  have := fun i ↦ (fun i ↦ hs_dir _ (a i)) _ (h_mem_a i)
  have := fun j ↦ this _ _ (h_mem_b j)
  let max : (j : ι) → α j := fun j ↦ Exists.choose <| this j
  let h_max_mem : ∀ j, max j ∈ s j := fun j ↦ Exists.choose_spec (this j) |>.1
  have h_max_le_a : ∀ j, a j ≤ max j := fun j ↦ Exists.choose_spec (this j) |>.2.1
  have h_max_le_b : ∀ j, b j ≤ max j := fun j ↦ Exists.choose_spec (this j) |>.2.2
  use max
  refine ⟨?_, ?_, ?_⟩
  . simp only [Set.mem_pi, Set.mem_univ, forall_true_left, implies_true, *]
  . assumption
  . assumption

-- Lemma 16.(i)
lemma Set.Pi.nonempty (hs_ne : ∀ i, Set.Nonempty (s i)) :
  Set.Nonempty <| Set.pi (@Set.univ ι) s := Set.univ_pi_nonempty_iff.mpr hs_ne

noncomputable def Set.Nonempty.choose {α : Type*} {s : Set α} (h_ne : s.Nonempty) : s :=
  have : ∃ a, a ∈ s := by assumption
  ⟨Exists.choose this, Exists.choose_spec this⟩


open Classical in
noncomputable def Set.Pi.extend {ι : Type*} {α : ι → Type*}
  {s : (i : ι) → Set (α i)} (i : ι) (a : α i) (h_mem_a : a ∈ s i)
  (h_ne : ∀ i, Set.Nonempty (s i)) :
  (j : ι) → α j := fun j ↦ if h' : i = j then cast (congr rfl h') a else Exists.choose (h_ne j)

lemma Set.Pi.extend_spec {ι : Type*} {α : ι → Type*}
  {s : (i : ι) → Set (α i)} {i : ι} {a : α i} {h_mem_a : a ∈ s i}
  {h_ne : ∀ i, Set.Nonempty (s i)} :
  ∀ j, Set.Pi.extend _ a h_mem_a h_ne j ∈ s j := by
  intros j
  by_cases h' : i = j
  . subst h'
    simp [*, extend, cast_eq]
  . simp [*, extend]
    exact Exists.choose_spec _


-- Lemma 16.(ii)
open Classical in
lemma proj_is_fiber_of_ne (hs_ne : ∀ i, Set.Nonempty (s i)) (i : ι) : (S ⇓ i) = s i := by
  -- simp [proj]
  ext a
  constructor <;> intros h
  . simp only [proj, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_setOf_eq] at h
    aesop?
  . simp only [proj, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_setOf_eq]
    use Set.Pi.extend _ a h hs_ne
    constructor
    . exact Set.Pi.extend_spec
    . simp? [Set.Pi.extend, cast_eq]


#check Pi.supSet

-- Lemma 16.(iii)
lemma sSup_pi_eq_proj (hs_dir : ∀ i, DirectedOn (. ≤ .) (s i)) (hs_ne : ∀ i, Set.Nonempty (s i)) :
  sSup S = fun j ↦ (sSup <| s j) := by
  ext j
  rw [← proj_is_fiber_of_ne _ hs_ne]
  rw [← proj_eq_sSup (Pi.directed _ hs_dir)]

end Lemma16










end Pi
