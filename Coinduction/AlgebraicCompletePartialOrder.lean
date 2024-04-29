import Coinduction.CompletePartialOrder
import Coinduction.Ideal
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

def IsεδContinuous (f : α → β) : Prop :=
  ∀ a : α, ∀ ε : β, IsCompactElement ε → ε ≤ f a → ∃ δ : α, IsCompactElement δ ∧ δ ≤ a ∧ ε ≤ f δ

#check DirectedOn.IsLUB.sSup_eq
#print IsCompactElement
lemma εδ_continuous_of_continuous (f : α → β) (hcont : ScottContinuous f) : IsεδContinuous f := by
  have hmono : Monotone f := hcont.monotone
  intros a ε hcomp_ε h_e_le_fa
  have h_a_eq_sup := AlgebraicCompletePartialOrder.compactly_generated a
  have := CompletePartialOrder.scottContinuous.1 hcont (CompletePartialOrder.compacts_le_nonempty _) (AlgebraicCompletePartialOrder.compacts_le_directed a)
  rw [← h_a_eq_sup] at this
  have h_fcomp_dir : DirectedOn (. ≤ .) (f '' CompactsLe a) := (directedOn_image' f hcont (CompletePartialOrder.compacts_le_nonempty a) (compacts_le_directed a))
  have : sSup (f '' CompactsLe a) = f a := DirectedOn.IsLUB.sSup_eq h_fcomp_dir this
  rw [← this] at h_e_le_fa
  have ⟨δ, ⟨hδ_mem, hδ_le⟩⟩ := hcomp_ε _ (h_fcomp_dir) (Set.nonempty_image_iff.2 (CompletePartialOrder.compacts_le_nonempty a)) h_e_le_fa
  choose δ' hδ' using hδ_mem
  use δ'
  refine ⟨?_, ?_, ?_⟩




section
  open CompletePartialOrder

  variable {ι : Type} {α : Type} [AlgebraicCompletePartialOrder α]

  lemma compact_values_of_compact {f : ι → α} : IsCompactElement f → ∀ i, IsCompactElement (f i) := by
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


  lemma compact_iff_finite_support_and_compact_values {f : ι → α} :
    IsCompactElement f ↔ (Set.Finite (support f) ∧ ∀ a, IsCompactElement (f a)) := by
    constructor
    . intros h
      constructor
      . apply finite_support_of_compact h
      . apply compact_values_of_compact h
    . rintro ⟨h_finite_supp, h_comp_val⟩
      exact CompletePartialOrder.compact_of_finite_support_and_compact_values h_finite_supp h_comp_val

end


section Exponential

  variable {ι : Type} {α : Type} [AlgebraicCompletePartialOrder α]

  example (s t : Set α) (hs : s.Finite) (ht : t.Finite) : (s ∪ t).Finite := by exact?
  #check Set.Finite.subset

  lemma AlgebraicCompletePartialOrder.Pi.compacts_le_directed (f : ι → α) :
    DirectedOn (. ≤ .) (CompactsLe f) := by
    rintro x ⟨h_comp_x, h_le_x_f⟩ y ⟨h_comp_y, h_le_y_f⟩
    rw [compact_iff_finite_support_and_compact_values] at h_comp_x h_comp_y
    rcases h_comp_x with ⟨h_fin_supp_x, h_comp_x⟩
    rcases h_comp_y with ⟨h_fin_supp_y, h_comp_y⟩
    have : ∀ i, ∃ w, x i ≤ w ∧ w ≤ f i ∧ y i ≤ w ∧ IsCompactElement w ∧ (i ∉ support x ∧ i ∉ support y → w = ⊥) := by
      intros i
      specialize h_le_x_f i
      specialize h_le_y_f i
      specialize h_comp_x i
      specialize h_comp_y i
      have := AlgebraicCompletePartialOrder.compactly_generated (f i)
      rw [this] at h_le_x_f h_le_y_f ; clear this
      specialize h_comp_x _ (AlgebraicCompletePartialOrder.compacts_le_directed _) (CompletePartialOrder.compacts_le_nonempty _) h_le_x_f
      specialize h_comp_y _ (AlgebraicCompletePartialOrder.compacts_le_directed _) (CompletePartialOrder.compacts_le_nonempty _) h_le_y_f
      rcases h_comp_x with ⟨x', h_comp_x', h_le_x_x'⟩
      rcases h_comp_y with ⟨y', h_comp_y', h_le_y_x'⟩
      have := AlgebraicCompletePartialOrder.compacts_le_directed (f i)
      specialize this _ h_comp_x' _ h_comp_y'
      rcases this with ⟨z, ⟨h_comp_z, h_z_le_f⟩, h_le_x'_z, h_le_y'_z⟩
      by_cases h_i_supp_x : i ∈ support x <;> by_cases h_i_supp_y : i ∈ support y
      all_goals (
        try (
            use z
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            . exact le_trans h_le_x_x' h_le_x'_z
            . exact h_z_le_f
            . exact le_trans h_le_y_x' h_le_y'_z
            . exact h_comp_z
            . rintro ⟨_, _⟩
              contradiction
            )
      )
      . use ⊥
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        . simp_all [support]
        . simp_all [support]
        . simp_all [support]
        . exact CompletePartialOrder.bot_compact
        . intros ; rfl
    choose g hg using this
    use g
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    . rw [compact_iff_finite_support_and_compact_values]
      constructor
      . have : support g ⊆ support x ∪ support y := by
          intros i
          have := (hg i).2.2.2.2
          contrapose
          sorry --set things
        exact Set.Finite.subset (Set.Finite.union h_fin_supp_x h_fin_supp_y) this
      . intros i ; exact (hg i).2.2.2.1
    . intros i ; exact (hg i).2.1
    . intros i ; exact (hg i).1
    . intros i ; exact (hg i).2.2.1






#check proj_directed

  open Classical in
  lemma AlgebraicCompletePartialOrder.Pi.compactly_generated (f : ι → α) :
    f = sSup (CompactsLe f) := by
    ext i
    rw [AlgebraicCompletePartialOrder.compactly_generated (f i)]
    apply le_antisymm
    . apply DirectedOn.sSup_le_sSup_of_forall_exists_le
        (AlgebraicCompletePartialOrder.compacts_le_directed _)
        (proj_directed (AlgebraicCompletePartialOrder.Pi.compacts_le_directed f) i)
      rintro b ⟨h_b_le_f, h_comp_b⟩
      use b
      refine ⟨?_, le_rfl⟩
      let w : ι → α := fun j ↦ if j = i then b else ⊥
      use w
      refine ⟨⟨?_, ?_⟩, ?_⟩
      . rw [compact_iff_finite_support_and_compact_values]
        constructor
        . have : support w ⊆ {i} := by intros _ ; simp_all [support]
          exact Set.Finite.subset (Set.finite_singleton i) this
        . intros j
          by_cases j = i
          . simp_all
          . simp_all [CompletePartialOrder.bot_compact]
      . intros j
        by_cases j = i
        . simp_all
        . simp_all
      . simp_all
    . apply DirectedOn.sSup_le_sSup_of_forall_exists_le
        (proj_directed (AlgebraicCompletePartialOrder.Pi.compacts_le_directed f) i)
        (AlgebraicCompletePartialOrder.compacts_le_directed _)
      rintro j ⟨g, ⟨⟨h_comp_g, h_le_g_f⟩, h_eq_g_i_j⟩⟩
      use j
      rw [compact_iff_finite_support_and_compact_values] at h_comp_g
      refine ⟨⟨?_, ?_⟩, le_rfl⟩
      . rw [← h_eq_g_i_j]
        exact h_comp_g.2 i
      . rw [← h_eq_g_i_j]
        exact h_le_g_f _


  instance : AlgebraicCompletePartialOrder (ι → α) where
    compactly_generated := AlgebraicCompletePartialOrder.Pi.compactly_generated
    compacts_le_directed := AlgebraicCompletePartialOrder.Pi.compacts_le_directed

end Exponential
