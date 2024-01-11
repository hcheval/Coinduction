import Mathlib
import Coinduction.Playground

open OmegaCompletePartialOrder

set_option autoImplicit false

local notation "ωContinuous" => OmegaCompletePartialOrder.Continuous



section Kleene

  variable {α : Type} [OmegaCompletePartialOrder α] [OrderBot α]
  variable (f : α →o α)

  lemma increasing_iterate : ∀ n, f^[n] ⊥ ≤ f^[n + 1] ⊥ := by
    intros n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      have : Monotone f := by exact?
      rw [Function.iterate_succ_apply']
      rw [Function.iterate_succ_apply']
      exact f.mono ih

  def Chain.iterate : Chain α where
    toFun := fun n ↦ f^[n] ⊥
    monotone' := monotone_nat_of_le_succ (increasing_iterate f)

  lemma chain_def : ∀ i, Chain.iterate f i = f^[i] ⊥ := fun i => rfl

  lemma chain_succ : ∀ i, Chain.iterate f (i + 1) = f (Chain.iterate f i) := by
    intros i
    rw [chain_def, chain_def]
    rw [Function.iterate_succ_apply']

  def lfp := ωSup (Chain.iterate f)

  -- to write properly, but aesop is amazing
  lemma lub_union_bot (s : Set α) (b) : IsLUB s b ↔ IsLUB (s ∪ {⊥}) b := by
    constructor <;> intros h <;> cases h <;> constructor <;> aesop?

  def shift_chain (c : Chain α) : Chain α where
    toFun := fun n ↦ c (n + 1)
    monotone' := by
      intros a b le
      have : a + 1 ≤ b + 1 := by exact?
      apply c.mono this

  lemma range_shift : Set.range (Chain.iterate f) = Set.range (shift_chain (Chain.iterate f)) ∪ {⊥} := by
    ext x
    constructor
    . intros h_mem
      rcases h_mem with ⟨i, hi⟩
      by_cases h : x = ⊥
      . apply Or.inr <;> aesop?
      . cases i with
        | zero =>
          apply False.elim
          have : Chain.iterate f 0 = ⊥ := rfl
          rw [this] at hi
          symm at hi
          contradiction
        | succ i =>
          apply Or.inl
          simp only [Set.mem_range]
          use i
          have : shift_chain (Chain.iterate f) i = Chain.iterate f (i + 1) := rfl
          rw [this]
          exact hi
    . intros h_mem
      rcases h_mem with h_mem_l | h_mem_r
      . rcases h_mem_l with ⟨i, hi⟩
        use i + 1
        exact hi
      . use 0
        have : x = ⊥ := by exact?
        rw [this]
        rfl





  lemma sup_shift : ωSup (Chain.iterate f) = ωSup (shift_chain (Chain.iterate f)) := by
    -- refine ωSup_eq_of_isLUB ?h
    refine (ωSup_eq_of_isLUB ?h).symm
    rw [range_shift]
    rw [← lub_union_bot]
    exact isLUB_range_ωSup (shift_chain (Chain.iterate f))




  def lfp_is_fixedpoint (f_cont : ωContinuous f) : f (lfp f) = lfp f := by
    unfold lfp
    rw [f_cont]
    have : (Chain.iterate f).map f = shift_chain (Chain.iterate f) := sorry
    rw [this]
    rw [sup_shift]

  lemma least_aux (x) : f x = x → ∀ i, Chain.iterate f i ≤ x := by
    intros h i
    induction i with
    | zero =>
      exact bot_le
    | succ i ih =>
      rw [chain_succ]
      rw [← h]
      exact f.mono ih



  def lfp_is_least : ∀ x, f x = x → lfp f ≤ x := by
    intros x h_fix
    unfold lfp
    have := least_aux f x h_fix
    exact ωSup_le (Chain.iterate f) x this

end Kleene

def Chain.identity : Chain ℕ where
  toFun := id
  monotone' := by exact monotone_id

section
  variable {α β : Type} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]

  def funChain (f : WithTop ℕ →o α) : Chain α where
    toFun := fun i ↦ f i
    monotone' := by
      intros a b le
      apply f.mono
      exact WithTop.coe_mono le

  def topIdChain : Chain (WithTop ℕ) where
    toFun := fun i ↦ i
    monotone' := Nat.mono_cast

  lemma topIdChain_sup_top : ωSup topIdChain = ⊤ := sorry



  lemma ωSup_of_topIdChain (f : WithTop ℕ →o α) (mono : Monotone f)
    (cont : ωContinuous f)
    : ωSup (funChain f) = f ⊤ := by
    let c₁ : Chain (WithTop ℕ) := ⟨fun i => ↑i, by exact?⟩

    let f' : ℕ →o α := ⟨fun (i : ℕ) ↦ f i, (by intros _ _ _; apply f.mono; exact WithTop.coe_mono (by assumption))⟩
    have : funChain f = c₁.map f := rfl
    rw [this]
    rw [← cont]
    have : ωSup c₁ = ⊤ := by sorry -- obvious
    rw [this]


  #check Chain
  def HaddockContinuous (f : α →o β) :=
    ∀ h : WithTop ℕ →o α, ωContinuous h → ωContinuous ⟨f ∘ h, Monotone.comp f.mono h.mono⟩

  def HaddockContinuous' (f : α → β) :=
    Monotone f ∧ ∀ h : WithTop ℕ → α, Continuous' h → Continuous' (f ∘ h)

  lemma haddock_continuous_of_bundled (f : α →o β) : HaddockContinuous f → HaddockContinuous' f := by
    intros hadd
    apply And.intro f.mono
    intros h h_cont
    specialize hadd ⟨h, Continuous'.to_monotone h_cont⟩ (Continuous'.to_bundled h h_cont)
    exact Continuous.of_bundled _ _ hadd

  lemma haddock_continuous_to_bundled (f : α →o β) (hadd : HaddockContinuous' f) : HaddockContinuous f := by
    intros h h_cont
    have := hadd.2 h (continuous'_coe.mpr h_cont)
    exact Continuous'.to_bundled (↑f ∘ ↑h) this


  def chainTopExtFun (c : Chain α) : WithTop ℕ → α :=
    fun n ↦ match n with
    | ⊤ => ωSup c
    | WithTop.some n' => c n'

  lemma chainTopExtMono (c : Chain α) : Monotone (chainTopExtFun c) :=
    fun i j h_le => match i, j with
    | ⊤, ⊤ => le_rfl
    | WithTop.some i', WithTop.some j' => by
      dsimp only [chainTopExtFun]; apply c.mono; exact (WithTop.le_coe rfl).mp h_le
    | ⊤, WithTop.some j' => by
      dsimp only [chainTopExtFun]
      rw [top_le_iff] at h_le
      have := WithTop.nat_ne_top j' h_le
      contradiction
    | WithTop.some i', ⊤ => by dsimp only [chainTopExtFun]; exact le_ωSup c i'

  -- def chainTopExtCont (c : Chain α) : Continuous' (chainTopExtFun c) :=
  --   ⟨chainTopExtMono _,
  --     by
  --   ⟩

  example (f : WithTop ℕ →o WithTop ℕ) : ωContinuous f := by
    intros c
    refine ωSup_eq_of_isLUB ?h
    unfold IsLUB IsLeast lowerBounds
    cases ωSup c with
    | none =>
      constructor
      . sorry
      . aesop?
    | some m => sorry

  example [Inhabited α] : ¬(∀ x : α, ¬p x) → (∃ x : α, p x) := by
    exact fun a => (fun {α} {p} => not_forall_not.mp) a


  def chainTopExt (c : Chain α) : WithTop ℕ →o α := ⟨chainTopExtFun c, chainTopExtMono c⟩

  lemma ωcontinuous_of_haddock_continuous (f : α →o β) (hadd : HaddockContinuous f) :
    ωContinuous f := by
    intros c
    let h' : WithTop ℕ →o α := chainTopExt c
    have h'_cont : ωContinuous h' := sorry
    have : h' ⊤ = ωSup c := rfl
    rw [← this]; clear this
    let c₁ : Chain α := funChain h'
    have : c = c₁ := rfl
    rw [this]; clear this
    have : topIdChain.map h' = c₁ := rfl
    rw [← this]; clear this
    let fh : WithTop ℕ →o β := ⟨f ∘ h', Monotone.comp f.mono h'.mono⟩
    have : (topIdChain.map h').map f = topIdChain.map fh := rfl
    rw [this]; clear this
    have : ωContinuous fh := hadd h' h'_cont
    rw [← this]; clear this
    rw [topIdChain_sup_top]
    rfl



  variable [OrderBot α]
  lemma haddock_fixedpoint (f : α →o α) (hadd : HaddockContinuous f) :
    f (lfp f) = lfp f ∧ (∀ x, f x = x → lfp f ≤ x) := by
    have : ωContinuous f := ωcontinuous_of_haddock_continuous f hadd
    constructor
    . apply lfp_is_fixedpoint f this
    . apply lfp_is_least f

end

/-
  f : γ → α → β cont
  f (sSup s) = sSup (f '' s : Set (α → β))   (: α → β)
  a : α

  ⊢ (f . a) (sSup s) = sSup ((f . a) '' s)   (: β)
-/
section
  variable {α β γ : Type} [OmegaCompletePartialOrder β] [OmegaCompletePartialOrder γ]

  lemma pointwise_cont_of_cont (f : γ → α → β) : Continuous' f → (∀ a : α, Continuous' <| fun c ↦ f c a) :=
    fun h a ↦ Continuous.of_bundled _ (fun _ _ hle ↦ h.to_monotone hle _) (fun _ ↦ congr_fun (h.to_bundled _ _) a)

  lemma cont_of_pointwise_cont (f : γ → α → β) : (∀ a : α, Continuous' <| fun c ↦ f c a) → Continuous' f :=
    fun h ↦ Continuous.of_bundled _
      (fun _ _ h' a ↦ h a |>.to_monotone h')
      (by intro c; ext a; apply (h a).to_bundled _ c)

  lemma pointwise_cont_cont (f : γ → α → β) : Continuous' f ↔ (∀ a, Continuous' <| fun c ↦ f c a) :=
    ⟨pointwise_cont_of_cont _, cont_of_pointwise_cont _⟩

end
section
  variable {α : Type} {β : Type} [OmegaCompletePartialOrder β]

  -- example (g : WithTop ℕ →o α → β) :
  --   Monotone g ↔ (∀ a, Monotone (fun n ↦ g n a)) := by
  --     constructor <;> intros _
  --     . intros a
  --       intros x y hle
  --       dsimp only
  --       apply g.mono hle
  --     . intros x y hle
  --       apply g.mono hle


  -- example (g : WithTop ℕ → α → β) :
  --   Monotone g ↔ (∀ a, Monotone (fun n ↦ g n a)) := by
  --     constructor <;> intros h
  --     . intros a
  --       intros x y hle
  --       dsimp only
  --       apply h hle
  --     . intros x y hle a
  --       apply h _ hle

  -- example (g : WithTop ℕ →o α → β) :
  --   Monotone g ↔ (∀ a, Monotone (fun n ↦ g n a)) := by
  --     constructor <;> intros _
  --     . intros a
  --       intros x y hle
  --       dsimp only
  --       apply g.mono hle
  --     . intros x y hle
  --       apply g.mono hle

  -- example (f : (α → β) →o (α → β)) :
  --   (∀ g : WithTop ℕ →o α → β, (ωContinuous g) → ωContinuous (f.comp g)) → HaddockContinuous f := by
  --     intros h
  --     intros φ hφ
  --     specialize h φ hφ

φ : Formula → Option (Γ ⊢ φ)

  lemma haddock_continuous_functional' (f : (α → β) → (α → β)) :
    Monotone f ∧
    (∀ g : WithTop ℕ → α → β, (∀ a, Continuous' <| fun n ↦ g n a) → ∀ a, Continuous' <| fun n ↦ (f (g n) a)) → HaddockContinuous' f := by
      rintro ⟨f_mono, h⟩
      apply And.intro f_mono
      intros φ hφ
      specialize h φ
      rw [pointwise_cont_cont] at hφ
      specialize h hφ
      rw [← pointwise_cont_cont] at h
      have : f ∘ φ = fun n a ↦ f (φ n) a := rfl
      rw [this] -- this is useless
      exact h

  lemma haddock_continuous_functional (f : (α → β) →o (α → β)) :
    (∀ g : WithTop ℕ → α → β, (∀ a, Continuous' <| fun n ↦ g n a) → ∀ a, Continuous' <| fun n ↦ (f (g n) a)) → HaddockContinuous f :=
    fun h ↦ haddock_continuous_to_bundled _ (haddock_continuous_functional' _ ⟨f.mono, h⟩)


  variable [OrderBot β]
  lemma haddock_fixedpoint_functional (f : (α → β) →o (α → β)) :
    (∀ g : WithTop ℕ → α → β, (∀ a, Continuous' <| fun n ↦ g n a)
    → ∀ a, Continuous' <| fun n ↦ (f (g n) a)) →
    f (lfp f) = lfp f ∧ (∀ x, f x = x → lfp f ≤ x) :=
    fun h ↦ haddock_fixedpoint _ <| haddock_continuous_to_bundled _ (haddock_continuous_functional' _ ⟨f.mono, h⟩)
    -- by
    --   intros h
    --   have : HaddockContinuous' f := haddock_continuous_functional' _ ⟨f.mono, h⟩
    --   have : HaddockContinuous f := haddock_continuous_to_bundled _ this
    --   exact haddock_fixedpoint _ this


  #check Continuous'
end

#check DirectedOn

/-
  sup c = ⊤
  f (c n) ≤ f ⊤
  ok pt ca f monotona

  sup c = a
  f (c n) ≤ f a
  ok pt ca f monotona

  => f (sup c) ∈ UB (f c)


  sup c = ⊤
  pp f a ∈ UB (f c) ≤
-/
