import Coinduction.Embedding

open CompletePartialOrder (IsCompactElement CompactsLe)

set_option autoImplicit false

variable {α β : Type*} [AlgebraicCompletePartialOrder α] [AlgebraicCompletePartialOrder β]

#check MonotoneOn

structure Lifting (f : α → β) where
  (h_comp : ∀ (a : α), IsCompactElement a → IsCompactElement (f a))
  (h_mono : MonotoneOn f {a | IsCompactElement a})

def lift (f : α → β)
  -- (h_comp : ∀ (a : α), IsCompactElement a → IsCompactElement (f a))
  -- (h_mono : MonotoneOn f {a | IsCompactElement a})
  : α → β :=
  fun a ↦ sSup <| f '' (CompactsLe a)

lemma directed_of_monotone_on {f : α → β} :
  ∀ {d : Set α}, MonotoneOn f d → DirectedOn (. ≤ .) d → DirectedOn (. ≤ .) (f '' d) := by
  intros d h_mono h_dir
  unfold DirectedOn
  intros b h_mem_b b' h_mem_b'
  rcases h_mem_b with ⟨a, ⟨h_mem_a, h_eq_a⟩⟩
  rcases h_mem_b' with ⟨a', ⟨h_mem_a', h_eq_a'⟩⟩
  unfold DirectedOn at h_dir
  specialize h_dir _ h_mem_a _ h_mem_a'
  aesop?


attribute [simp] CompactsLe in
lemma lifting_directed {f : α → β}
  -- (h_comp : ∀ (a : α), IsCompactElement a → IsCompactElement (f a))
  (h_mono : MonotoneOn f {a | IsCompactElement a}) :
  ∀ a : α, DirectedOn (. ≤ .) (f '' CompactsLe a) := by
  intros a
  apply directed_of_monotone_on
  . intros a' h_mem_a' a'' h_mem_a'' h_le
    apply h_mono <;> simp_all
  . exact AlgebraicCompletePartialOrder.compacts_le_directed a

lemma lifting_nonempty {f : α → β} (a : α) : Set.Nonempty <| f '' CompactsLe a :=
  Set.Nonempty.image _ <| CompletePartialOrder.compacts_le_nonempty _

variable {f : α → β} (f_lifting : Lifting f)

@[simp]
lemma lift_extension : ∀ (a : α), IsCompactElement a → lift f a = f a := by
  intros a h_comp_a
  unfold lift
  sorry

example (α β : Type) (s : Set α) (h : s.Nonempty) (f : α → β) : (f '' s).Nonempty := by
  exact?

lemma compact_of_mem_lifting_image : ∀ {a : α} {b : β}, b ∈ f '' CompactsLe a → IsCompactElement b := by
  intros a b h_mem
  rcases f_lifting with ⟨f_comp, _⟩
  aesop?

lemma compacts_le_trans {a₁ a₂ : α} : a₁ ≤ a₂ → CompactsLe a₁ ⊆ CompactsLe a₂ := by
  intros h_le a h_mem
  have : a ≤ a₂ := le_trans h_mem.2 h_le
  simp_all

example (s₁ s₂ : Set α) (h : s₁ ⊆ s₂) : f '' s₁ ⊆ f '' s₂ := by exact?

lemma lift_mono : Monotone (lift f) := by
  unfold lift Monotone
  intros a₁ a₂ h_le
  dsimp only
  rcases f_lifting with ⟨f_comp, f_mono⟩
  apply CompletePartialOrder.forall_exists_le_iff_sSup_le_sSup
    (lifting_directed f_mono _)
    (lifting_directed f_mono _)
    (Set.Nonempty.image _ <| CompletePartialOrder.compacts_le_nonempty _)
    (fun b h ↦ compact_of_mem_lifting_image ⟨f_comp, f_mono⟩ h) |>.mp
  intros b h_mem
  -- is this how they did it in Coq? It seemed more complicated
  use b
  have : b ∈ f '' CompactsLe a₂ := (Set.image_subset f (compacts_le_trans h_le)) h_mem
  simp_all

lemma lift_εδ_continuous : IsεδContinuous (lift f) := by
  intros ε δ h_comp_δ h_le
  unfold IsCompactElement at h_comp_δ
  specialize h_comp_δ (f '' CompactsLe ε) (lifting_directed f_lifting.h_mono _) (lifting_nonempty _) h_le
  rcases h_comp_δ with ⟨b, ⟨h_mem_b, h_le_b⟩⟩
  rcases h_mem_b with ⟨b', ⟨⟨hb'_comp, hb'_le⟩, hb'_eq⟩⟩
  use b'
  refine ⟨by assumption, by assumption, ?_⟩
  have : f b' ≤ lift f b' := by rw [lift_extension _ hb'_comp]
  rw [← hb'_eq] at h_le_b
  exact le_trans h_le_b this

lemma lift_continuous : Continuous (lift f) := by
  

section

  open Classical

  variable {α β : Type} [PartialOrder α] [OrderBot α] [PartialOrder β] [OrderBot β]
  variable {α' β' : Type} [AlgebraicCompletePartialOrder α'] [AlgebraicCompletePartialOrder β']

  variable
    (f : α → β)
    (e₁ : AlgebraicCompletePartialOrder.Embedding α α')
    (e₂ : AlgebraicCompletePartialOrder.Embedding β β')

  @[simp] noncomputable def bot_ext : α' → β' :=
    fun a => if IsCompactElement a then e₂.toFun (f (e₁.invFun a)) else ⊥

  @[simp] lemma bot_ext_compact {a : α'} :
    IsCompactElement a → bot_ext f e₁ e₂ a = e₂.toFun (f (e₁.invFun a)) := by
    intros h
    simp? [*, bot_ext]

  @[simp] lemma bot_ext_not_compact {a : α'} :
    ¬IsCompactElement a → bot_ext f e₁ e₂ a = ⊥ := by
    intros h
    simp? [*, bot_ext]

  @[simp] noncomputable def lift_bot_ext: α' → β' :=
    lift (bot_ext f e₁ e₂)

-- i think i was stupid
  -- lemma lift_bot_ext_lifting
  --   (f_mono : Monotone f)
  --   : Lifting (lift_bot_ext f e₁ e₂) := by
  --   constructor
  --   . intros a h_comp_a
  --     unfold lift_bot_ext
  --     rw [lift_extension _ h_comp_a, bot_ext_compact _ _ _ h_comp_a]
  --     apply AlgebraicCompletePartialOrder.Embedding.to_fun_compact
  --   . intros x₁ h_mem_x₁ x₂ h_mem_x₂ h_le
  --     unfold lift_bot_ext
  --     rw [lift_extension _ h_mem_x₁, bot_ext_compact _ _ _ h_mem_x₁]
  --     rw [lift_extension _ h_mem_x₂, bot_ext_compact _ _ _ h_mem_x₂]
  --     rw [← AlgebraicCompletePartialOrder.Embedding.to_fun_bimono]
  --     apply f_mono
  --     rw [← AlgebraicCompletePartialOrder.inv_fun_bimonotone _ _ _ h_mem_x₁ h_mem_x₂]
  --     assumption
  --   done

  lemma bot_ext_lifting :
    Monotone f → Lifting (bot_ext f e₁ e₂) := by
    intros f_mono
    constructor
    . intros a h_comp_a
      rw [bot_ext_compact _ _ _ h_comp_a]
      apply AlgebraicCompletePartialOrder.Embedding.to_fun_compact
    . intros x₁ h_mem₁ x₂ h_mem₂ h_le
      rw [bot_ext_compact _ _ _ h_mem₁]
      rw [bot_ext_compact _ _ _ h_mem₂]
      rw [← AlgebraicCompletePartialOrder.Embedding.to_fun_bimono]
      apply f_mono
      rw [← AlgebraicCompletePartialOrder.inv_fun_bimonotone _ _ _ h_mem₁ h_mem₂]
      assumption
    done

  lemma lift_bot_ext_monotone :
    Monotone f →
    Monotone (lift_bot_ext f e₁ e₂) :=
  by
    intros f_mono
    apply lift_mono
    apply bot_ext_lifting
    assumption

  lemma lift_bot_ext_continuous :
    Monotone f →
    Continuous (lift_bot_ext f e₁ e₂) :=
  by
    intros f_mono
    apply lift_continuous









end
