import Coinduction.CompletePartialOrder
import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Order.Directed

set_option autoImplicit false

#check OmegaCompletePartialOrder
open CompletePartialOrder (IsCompactElement CompactsLe)

class AlgebraicCompletePartialOrder (α : Type*) extends CompletePartialOrder α, OrderBot α where
  compactly_generated : ∀ a : α, a = sSup (CompactsLe a)
  compacts_le_directed : ∀ a : α, DirectedOn (. ≤ .) (CompactsLe a)

variable {α β : Type*} [AlgebraicCompletePartialOrder α] [AlgebraicCompletePartialOrder β]

-- def IsεδContinuous (f : α → β) : Prop :=
--   ∀ a : α, ∀ ε : β, IsCompactElement ε → ε ≤ f a → ∃ δ : α, IsCompactElement δ ∧ δ ≤ a ∧ ε ≤ f δ

namespace AlgebraicCompletePartialOrder

variable {α : Type*} [AlgebraicCompletePartialOrder α]

lemma eq_bot_of_compacts_le_bot {a : α} : CompactsLe a = {⊥} → a = ⊥ := by
  intros heq
  have h := compactly_generated a
  have h' := CompletePartialOrder.lubOfDirected _ (compacts_le_directed a)
  rw [← h, heq] at h'
  rcases h' with ⟨h'₁, h'₂⟩
  apply bot_unique
  apply h'₂
  intros b hb
  cases hb
  exact le_refl _

#check IsUpperSet

example (a : α) : a ∈ upperBounds (CompactsLe a) := by
  intros b h
  cases h
  assumption





section
  open CompletePartialOrder

  variable {ι : Type} {α : ι → Type} [∀ i, AlgebraicCompletePartialOrder <| α i]

  lemma compact_values_of_compact (f : (i : ι) → α i) : IsCompactElement f → ∀ i, IsCompactElement (f i) := by
    intros hf_comp i
    rw [compact_iff_compact_on_lower_set]
    intros s hs_dir hs_ne hs_lower h_le
    let g := fun s ↦ CompactsLe (f s)
    have h : ∀ i, DirectedOn (. ≤ .) (g i) := by
      intros i
      apply compacts_le_directed
    have := sSup_pi_eq_proj _ h (fun i ↦ compacts_le_nonempty _)
    have hg : g = fun s ↦ CompactsLe (f s) := rfl
    specialize hf_comp _ (Pi.directed g h) (Set.Pi.nonempty _ (fun i ↦ compacts_le_nonempty _))
    simp_rw [(rfl : g = fun s ↦ CompactsLe (f s))] at * ; clear hg
    rw [this] at hf_comp
    specialize hf_comp (fun j ↦ by rw [compactly_generated (f j)])
    rcases hf_comp with ⟨f', hf'₁, hf'₂⟩
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left] at hf'₁
    use (f' i)
    constructor
    . specialize hf'₁ i
      rcases hf'₁ with ⟨hf'_comp, hf'_le⟩
      specialize hf'_comp _ hs_dir hs_ne (le_trans hf'_le h_le)
      rcases hf'_comp with ⟨_, hf'_comp₁, hf'_comp₂⟩
      exact hs_lower hf'_comp₂ hf'_comp₁
    . exact hf'₂ i

  lemma compact_support_of_compact {f : (i : ι) → α i} : IsCompactElement f → Set.Finite (support f) := by
    intros hf_comp
    simp [IsCompactElement] at hf_comp
    





end

section Lemma17
  open CompletePartialOrder
  variable {ι : Type} {α : ι → Type} [∀ i, AlgebraicCompletePartialOrder (α i)]



end Lemma17
