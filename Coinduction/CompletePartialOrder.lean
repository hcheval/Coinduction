import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Set.Finite

set_option autoImplicit true
set_option relaxedAutoImplicit false

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

  def Compacts (α : Type*) [CompletePartialOrder α] := {a : α | IsCompactElement a}

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

def support {α : Type} {β : α → Type} [∀ a, Bot (β a)] (f : ∀ a, β a) :=
  {a | f a ≠ ⊥}

lemma mem_support_iff {α : Type} {β : α → Type} [∀ a, Bot (β a)] (f : ∀ a, β a) :
  ∀ a, a ∈ support f ↔ f a ≠ ⊥ := fun a => by simp? [support]

-- example (s t : Set Nat) (h : s ⊆ t) (h' : t.Finite) : s.Finite := by exact?

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

section
  open Classical
  #print DirectedOn

  #print Set.toFinset

  lemma Finset.insert_subset_set_iff {α} (a : α) (s : Finset α) (r : Set α) :
    (insert a s).toSet ⊆ r ↔ insert a s.toSet ⊆ r := by aesop?

  lemma finset_has_upper_of_subset_directed {α : Type} [PartialOrder α] (d : Set α) (hne : d.Nonempty) (hd : DirectedOn (. ≤ .) d)
    (s : Finset α) : s.toSet ⊆ d → ∃ y ∈ d, ∀ x ∈ s, x ≤ y := by
    induction s using Finset.induction with
    | empty => aesop?
    | @insert a s' hmem ih =>
      intros h'
      rw [Finset.insert_subset_set_iff] at h'
      rw [Set.insert_subset_iff] at h'
      rcases h' with ⟨h'_mem, h'_subset⟩
      specialize ih h'_subset
      choose y hy using ih
      choose y' hy' using hd a h'_mem y hy.1
      use y'
      constructor
      . exact hy'.1
      . intros x h_mem_x
        rw [Finset.mem_insert] at h_mem_x
        rcases h_mem_x with h_eq_x_a | h_mem_x_s'
        . aesop?
        . have := hy.2 x h_mem_x_s'
          exact le_trans this hy'.2.2


  #print Set.Finite.toFinset

  namespace CompletePartialOrder
  lemma compact_of_finite_support_and_compact_values {α β : Type} [CompletePartialOrder β] [OrderBot β] {f : α → β}
    : Set.Finite (support f) → (∀ a, IsCompactElement (f a)) → IsCompactElement f := by
    intros h_fin_supp h_comp_val
    rw [compact_iff_compact_on_lower_set]
    intros d h_dir h_ne h_lower h_f_le_sSup
    have : ∀ a, ∃ b, b ∈ d ⇓ a ∧ f a ≤ b := fun a ↦ h_comp_val a _ (proj_directed h_dir _) (proj_ne h_ne _) (h_f_le_sSup a)
    choose g hb using this
    have : ∀ a ∈ support f, (g a) ∈ d ⇓ a ∧ f a ≤ g a := by
      intros a _
      aesop?
    have : ∀ a ∈ support f, ∃ φ ∈ d, f a ≤ φ a := by
      intros a h_mem_a
      specialize this _ h_mem_a
      rcases this with ⟨⟨φ, h_mem_φ⟩, h_f_le_g⟩
      use φ
      rw [← h_mem_φ.2] at h_f_le_g
      exact ⟨h_mem_φ.1, h_f_le_g⟩
    choose φ hφ using this
    let φ' : α → α → β := fun a ↦ if h : a ∈ support f then φ a h else ⊥
    have hφ' : ∀ a ∈ support f, φ' a ∈ d ∧ f a ≤ φ' a a := by
      intros a h_mem_a
      simp? [*]
    have h_supp_has_upper : (φ' '' (support f) ⊆ d)
      → ∃ χ ∈ d, (∀ ψ ∈ φ' '' (support f), ψ ≤ χ) := by
      have h_aux : Set.Finite (φ' '' (support f)) := sorry
      have := finset_has_upper_of_subset_directed d h_ne h_dir (Set.Finite.toFinset h_aux)
      rw [Set.Finite.coe_toFinset] at this
      have h_aux' : ∀ x, x ∈ Set.Finite.toFinset h_aux ↔ x ∈ φ' '' (support f) := by simp?
      sorry
    have : φ' '' (support f) ⊆ d := by sorry
    have ⟨χ, χ_mem, χ_upper⟩ := h_supp_has_upper this
    use (fun a ↦ if a ∈ support f then φ' a a else ⊥)
    constructor
    . unfold IsLowerSet at h_lower
      apply h_lower (a := χ) ?_ χ_mem
      intros a
      by_cases h_mem_supp : a ∈ support f
      . simp only [h_mem_supp, dite_true, ite_true]
        aesop?
      . simp [h_mem_supp]
    . intros a
      by_cases h_mem_supp : a ∈ support f
      . simp only [h_mem_supp, dite_true, ite_true]
        specialize hφ' _ h_mem_supp
        simp only [h_mem_supp, dite_true] at hφ'
        exact hφ'.2
      . simp only [h_mem_supp, dite_false, Pi.bot_apply, ite_self, le_bot_iff]
        simp only [support, ne_eq, Set.mem_setOf_eq, not_not] at h_mem_supp
        exact h_mem_supp

  end CompletePartialOrder
end

def IsRestrictionOnSupport {α : Type} {β : α → Type} [∀ a, Bot (β a)] (f g : (a : α) → β a) : Prop :=
  support f ⊆ support g ∧
  ∀ a ∈ support f, f a = g a

def finiteRestrictions {α : Type} {β : α → Type} [∀ a, Bot (β a)] (g : (a : α) → β a) : Set ((a : α) → β a) :=
  {f | Set.Finite (support f) ∧ IsRestrictionOnSupport f g}

section FiniteRestrictions

  variable {α : Type} {β : Type} [CompletePartialOrder β] [OrderBot β]

  open CompletePartialOrder

  lemma finite_restrictions_ne (g : α → β) :
    Set.Nonempty (finiteRestrictions g) := by
    use fun _ => ⊥
    -- simp? [finiteRestrictions]
    constructor
    . simp? [support]
    . simp? [IsRestrictionOnSupport]
      constructor
      . simp? [support]
      . intros a hmem
        contradiction


  open Classical in
  noncomputable def imp  (b₁ b₂ : β) := if b₁ = ⊥ then b₂ else b₁

  attribute [simp] imp in

  lemma finite_restrictions_directed (g : α → β) :
    DirectedOn (. ≤ .) (finiteRestrictions g) := by
    intros f' hmem_f' g' hmem_g'
    use fun a => imp (f' a) (g' a)
    constructor <;> constructor
    . sorry
    . constructor
      . rintro a hmem_a
        simp? [support] at hmem_a ⊢
        by_cases h : f' a = ⊥
        . simp_rw [h] at hmem_a
          simp only [ite_true] at hmem_a
          simp only [finiteRestrictions, support, ne_eq, IsRestrictionOnSupport, Set.setOf_subset_setOf, Set.mem_setOf_eq] at hmem_g'
          aesop?
        . by_cases h' : g' a = ⊥
          . simp_rw [h, ite_false] at hmem_a
            simp only [finiteRestrictions, support, ne_eq, IsRestrictionOnSupport, Set.setOf_subset_setOf, Set.mem_setOf_eq] at hmem_g' hmem_f'
            have := hmem_f'.2.2 a hmem_a
            rwa [← this]
          . simp_rw [h, ite_false] at hmem_a
            simp only [finiteRestrictions, support, ne_eq, IsRestrictionOnSupport, Set.setOf_subset_setOf, Set.mem_setOf_eq] at hmem_g' hmem_f'
            rwa [← hmem_g'.2.2 a h']
      . intros a hmem_a
        simp only [support, imp, ne_eq, Set.mem_setOf_eq] at hmem_a
        simp? [finiteRestrictions, IsRestrictionOnSupport, support] at hmem_g' hmem_f'
        by_cases h : f' a = ⊥
        . aesop?
        . aesop?
    . intros a
      dsimp only
      by_cases h : f' a = ⊥
      . simp [h]
      . simp [h]
    . intros a
      dsimp only
      by_cases h : f' a = ⊥
      . simp [h]
      . simp [h]
        by_cases h' : g' a = ⊥
        . simp [h']
        . simp only [finiteRestrictions, support, ne_eq, IsRestrictionOnSupport, Set.setOf_subset_setOf, Set.mem_setOf_eq] at hmem_f' hmem_g'
          rw [hmem_f'.2.2 a h]
          rw [hmem_g'.2.2 a h']


    -- constructor
    -- . constructor
    --   . sorry
    --   . constructor
    --   . rintro ⟨a, hmem_a⟩
    --     simp? [support] at hmem_a
    --     by_cases h : f' a = ⊥
    --     . simp_rw [h] at hmem_a
    --       simp? at hmem_a
    --       exfalso
    -- . constructor
    --   . sorry

  open Classical in
  lemma mem_finite_restrictions_of_bot_update (f : α → β) (a : α) :
    (fun x => if x = a then f a else ⊥ : α → β) ∈ finiteRestrictions f := by
    constructor
    . by_cases h : f a = ⊥
      . have : support (fun x => if x = a then f a else ⊥) = {} := by simp [support, *]
        rw [this]
        exact Set.finite_empty
      . have : support (fun x => if x = a then f a else ⊥) = {a} := by simp [support, *]
        rw [this]
        exact Set.finite_singleton _
    . constructor
      . intros a' hmem_a'
        simp? [support] at hmem_a'
        simp? [support, *]
      . intros a' hmem_a'
        simp? [support] at hmem_a'
        simp? [support, *]






  lemma is_lub_finite_restrictions (f : α → β) :
    IsLUB (finiteRestrictions f) f := by
    constructor
    . intros g hmem_g a
      rcases hmem_g with ⟨hmem_g₁, hmem_g₂⟩
      by_cases h : g a = ⊥
      . rw [h] ; exact bot_le
      . simp only [IsRestrictionOnSupport] at hmem_g₂
        have := hmem_g₂.2 a (by aesop?)
        rw [this]
    . intros g hg_upper a
      simp [upperBounds] at hg_upper
      specialize hg_upper (mem_finite_restrictions_of_bot_update _ a)
      specialize hg_upper a
      simp only [ite_true] at hg_upper
      exact hg_upper

  #check DirectedOn.IsLUB.sSup_eq

  lemma le_lub_finite_restrictions (f : α → β) :
    f ≤ sSup (finiteRestrictions f) := by
    rw [DirectedOn.IsLUB.sSup_eq (finite_restrictions_directed f) (is_lub_finite_restrictions f)]

  lemma support.subset_of_le {f g : α → β} :
    f ≤ g → support f ⊆ support g := by
    intros h a ha
    rw [mem_support_iff] at ha ⊢
    intros h'
    specialize h a
    rw [h'] at h
    have := eq_bot_iff.2 h
    contradiction



  lemma finite_support_of_compact {f : α → β} :
    IsCompactElement f → Set.Finite (support f) := by
    intros h_comp
    unfold IsCompactElement at h_comp
    have ⟨g, ⟨⟨h_finite_supp, _⟩, h_f_le_g⟩⟩ := h_comp _ (finite_restrictions_directed f) (finite_restrictions_ne f) (le_lub_finite_restrictions f)
    have := support.subset_of_le h_f_le_g
    exact Set.Finite.subset h_finite_supp this



end FiniteRestrictions


#check directedOn_image
#check Set.range
#check Set.nonempty_image_iff
lemma directedOn_image' {α β} [CompletePartialOrder α] [CompletePartialOrder β] (f : α → β) (h : ScottContinuous f) :
  ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (. ≤ .) d → DirectedOn (. ≤ .) (f '' d) := by
    intros d h_ne h_dir
    intros a h_a_mem y h_y_mem
    dsimp only
    choose a' ha' using h_a_mem
    choose y' hy' using h_y_mem
    choose z hz using h_dir a' ha'.1 y' hy'.1
    dsimp only at hz
    use f z
    refine ⟨?_, ?_, ?_⟩
    . aesop?
    . rw [← ha'.2]
      apply h.monotone
      exact hz.2.1
    . rw [← hy'.2]
      apply h.monotone
      exact hz.2.2
