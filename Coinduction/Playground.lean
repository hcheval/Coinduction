/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Directed
import Mathlib.Order.UpperLower.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.ContinuousFunction.Basic

/-!
# Scott topology

This file introduces the Scott topology on a preorder.

## Main definitions

- `preserve_lub_on_directed` - a function between preorders which preserves least upper bounds.
- `WithScottTopology.topological_space` - the Scott topology is defined as the join of the
  topology of upper sets and the topological space where a set `u` is open if, when the least upper
  bound of a directed set `d` lies in `u` then there is a tail of `d` which is a subset of `u`..

## Main statements

- `WithScottTopology.is_open_is_upper` - Scott open sets are upper
- `WithScottTopology.is_closed_is_lower` - Scott closed sets are lower
- `WithScottTopology.continuous_monotone` - Scott continuous functions are monotone.
- `preserve_lub_on_directed_iff_scott_continuity` - a function preserves least upper bounds of
  directed sets if and only if it is Scott continuous
- `WithScottTopology.t0_space` - the Scott topology on a partial order is T₀

## Implementation notes

A type synonym `WithScottTopology` is introduced and for a preorder `α`, `WithScottTopology α`
is made an instance of `topological_space` by the topology generated by the complements of the
closed intervals to infinity.
A class `Scott` is defined in `topology.omega_complete_partial_order` and made an instance of a
topological space by defining the open sets to be those which have characteristic functions which
are monotone and preserve limits of countable chains. Whilst this definition of the Scott topology
coincides with the one given here in some special cases, in general they are not the same
[Domain Theory, 2.2.4][abramsky_gabbay_maibaum_1994].

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]
* [Abramsky and Jung, *Domain Theory*][abramsky_gabbay_maibaum_1994]

## Tags
Scott topology, preorder
-/

variable (α β : Type _)

open Set

section preorder

variable {α} {β}

variable [Preorder α] [Preorder β]

lemma isUpperSet_iff_forall_le  {s : Set α} : IsUpperSet s ↔ ∀ ⦃a b : α⦄, a ≤ b →
  a ∈ s → b ∈ s := Iff.rfl

/--
The set of upper sets forms a topology
-/
def upperSetTopology : TopologicalSpace α :=
{ IsOpen := IsUpperSet,
  isOpen_univ := isUpperSet_univ,
  isOpen_inter := fun _ _ => IsUpperSet.inter,
  isOpen_sUnion := fun _ h => isUpperSet_sUnion h, }

end preorder

/--
Type synonym for a preorder equipped with the Scott topology
-/
def WithScottTopology := α

variable {α β}

namespace WithScottTopology

/-- `toScott` is the identity function to the `WithScottTopology` of a type.  -/
@[match_pattern] def toScott : α ≃ WithScottTopology α := Equiv.refl _

/-- `ofScott` is the identity function from the `WithScottTopology` of a type.  -/
@[match_pattern] def ofScott : WithScottTopology α ≃ α := Equiv.refl _

@[simp] lemma to_scott_symm_eq : (@toScott α).symm = ofScott := rfl
@[simp] lemma of_scott_symm_eq : (@ofScott α).symm = toScott := rfl
@[simp] lemma toScott_ofScott (a : WithScottTopology α) : toScott (ofScott a) = a := rfl
@[simp] lemma ofScott_toScott (a : α) : ofScott (toScott a) = a := rfl
-- porting note: removed @[simp] to make linter happy
lemma toScott_inj {a b : α} : toScott a = toScott b ↔ a = b := Iff.rfl
-- porting note: removed @[simp] to make linter happy
lemma ofScott_inj {a b : WithScottTopology α} : ofScott a = ofScott b ↔ a = b :=
Iff.rfl

/-- A recursor for `WithScottTopology`. Use as `induction x using WithScottTopology.rec`. -/
protected def rec {β : WithScottTopology α → Sort _}
  (h : ∀ a, β (toScott a)) : ∀ a, β a := fun a => h (ofScott a)


instance [Nonempty α] : Nonempty (WithScottTopology α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithScottTopology α) := ‹Inhabited α›

end WithScottTopology

section preorder

variable [Preorder α] [Preorder β]

instance : Preorder (WithScottTopology α) := ‹Preorder α›

instance : TopologicalSpace (WithScottTopology α) :=
  (upperSetTopology ⊔
    { IsOpen := fun u => ∀ (d : Set α) (a : α), d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB d a →
      a ∈ u → ∃ b ∈ d, (Ici b) ∩ d ⊆ u,
      isOpen_univ := by
        intros d _ hd₁ _ _ _
        cases' hd₁ with b hb
        use b
        constructor
        . exact hb
        . exact (Ici b ∩ d).subset_univ,
      isOpen_inter := by
        intros s t
        intros hs
        intro ht
        intros d a hd₁ hd₂ hd₃ ha
        obtain ⟨ b₁, ⟨hb₁_w, hb₁_h ⟩ ⟩  := hs d a hd₁ hd₂ hd₃ ha.1
        obtain ⟨ b₂, ⟨hb₂_w, hb₂_h ⟩ ⟩  := ht d a hd₁ hd₂ hd₃ ha.2
        rw [DirectedOn] at hd₂
        obtain ⟨ c, ⟨hc_w, hc_h ⟩ ⟩ := hd₂ b₁ hb₁_w b₂ hb₂_w
        use c
        constructor
        . exact hc_w
        . calc
            Ici c ∩ d ⊆ (Ici b₁ ∩ Ici b₂) ∩ d := by
            { apply inter_subset_inter_left d
              apply subset_inter (Ici_subset_Ici.mpr hc_h.1) (Ici_subset_Ici.mpr hc_h.2) }
            _ = ((Ici b₁)∩d) ∩ ((Ici b₂)∩d) := by rw [inter_inter_distrib_right]
            _ ⊆ s ∩ t := by { exact inter_subset_inter hb₁_h hb₂_h }
      isOpen_sUnion := by
        intros s h
        intros d a hd₁ hd₂ hd₃ ha
        rw [mem_sUnion] at ha
        obtain ⟨s₀, ⟨hs₀_w, hs₀_h⟩⟩ := ha
        obtain ⟨b, ⟨hb_w, hb_h⟩⟩ := h s₀ hs₀_w d a hd₁ hd₂ hd₃ hs₀_h
        use b
        constructor
        . exact hb_w
        . exact Set.subset_sUnion_of_subset s s₀ hb_h hs₀_w
      })

namespace WithScottTopology

lemma isOpen_eq_upper_and_LUB_mem_implies_tail_subset (u : Set (WithScottTopology α)) : IsOpen u
= (IsUpperSet u ∧ ∀ (d : Set α) (a : α), d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB d a → a ∈ u
  → ∃ b ∈ d, (Ici b) ∩ d ⊆ u) := rfl

lemma isOpen_iff_upper_and_LUB_mem_implies_inter_nonempty (u : Set (WithScottTopology α)) :
IsOpen u ↔ (IsUpperSet u ∧ ∀ (d : Set α) (a : α), d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB d a →
a ∈ u → (d ∩ u).Nonempty) := by
  rw [isOpen_eq_upper_and_LUB_mem_implies_tail_subset]
  constructor
  . refine' And.imp_right _
    intros h d a d₁ d₂ d₃ ha
    obtain ⟨b, ⟨h_1_w, h_1_h⟩⟩ := h d a d₁ d₂ d₃ ha
    rw [inter_nonempty_iff_exists_left]
    use b
    constructor
    . exact h_1_w
    . apply mem_of_subset_of_mem h_1_h
      rw [mem_inter_iff]
      constructor
      . exact left_mem_Ici
      . exact h_1_w
  . intros h
    constructor
    . exact h.1
    . intros d a d₁ d₂ d₃ ha
      have e1 : (d ∩ u).Nonempty := by exact h.2 d a d₁ d₂ d₃ ha
      rw [inter_nonempty_iff_exists_left] at e1
      obtain ⟨b, ⟨e1_h_w, e1_h_h⟩⟩ := e1
      use b
      constructor
      . exact e1_h_w
      . have e2 : Ici b ⊆ u := by exact isUpperSet_iff_Ici_subset.mp h.1 e1_h_h
        apply Subset.trans _ e2
        apply inter_subset_left

lemma isClosed_eq_lower_and_subset_implies_LUB_mem (s : Set (WithScottTopology α)) : IsClosed s
  = (IsLowerSet s ∧
  ∀ (d : Set α) (a : α), d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB d a → d ⊆ s → a ∈ s ) := by
  rw [← isOpen_compl_iff, isOpen_iff_upper_and_LUB_mem_implies_inter_nonempty,
    isLowerSet_compl.symm, compl_compl]
  refine' let_value_eq (And (IsLowerSet s)) _
  rw [eq_iff_iff]
  constructor
  . intros h d a d₁ d₂ d₃ d₄
    by_contra h'
    rw [← mem_compl_iff] at h'
    have c1: (d ∩ sᶜ).Nonempty := by exact h d a d₁ d₂ d₃ h'
    have c2: (d ∩ sᶜ) =  ∅ := by
      rw [← subset_empty_iff, ← inter_compl_self s]
      exact inter_subset_inter_left _ d₄
    rw [c2] at c1
    simp only [Set.not_nonempty_empty] at c1
  . intros h d a d₁ d₂ d₃ d₄
    by_contra h'
    rw [inter_compl_nonempty_iff, not_not] at h'
    have c1: a ∈ s := by exact h d a d₁ d₂ d₃ h'
    contradiction


lemma isOpen_isUpper {s : Set (WithScottTopology α)} : IsOpen s → IsUpperSet s := by
  intros h
  rw [isOpen_eq_upper_and_LUB_mem_implies_tail_subset] at h
  exact h.1

lemma isClosed_isLower {s : Set (WithScottTopology α)} : IsClosed s → IsLowerSet s := by
  intro h
  rw [isClosed_eq_lower_and_subset_implies_LUB_mem] at h
  exact h.1

/--
The closure of a singleton `{a}` in the Scott topology is the right-closed left-infinite interval
(-∞,a].
-/
@[simp] lemma closure_singleton (a : WithScottTopology α) : closure {a} = Iic a := by
  rw [← LowerSet.coe_Iic, ← lowerClosure_singleton]
  refine' subset_antisymm _ _
  . apply closure_minimal subset_lowerClosure
    rw [isClosed_eq_lower_and_subset_implies_LUB_mem]
    constructor
    . exact (lowerClosure {a}).lower
    . rw [lowerClosure_singleton]
      intros d b _ _ d₃ d₄
      rw [LowerSet.coe_Iic, mem_Iic]
      exact (isLUB_le_iff d₃).mpr d₄
  . apply lowerClosure_min subset_closure (isClosed_isLower _)
    apply isClosed_closure

lemma continuous_monotone {f : WithScottTopology α → WithScottTopology β}
  (hf : Continuous f) : Monotone f := by
  rw [Monotone]
  intros a b hab
  let u := (Iic (f b))ᶜ
  by_contra h
  have u2 : a ∈ (f⁻¹'  u) := h
  have s1 : IsOpen u
  { rw [isOpen_compl_iff, ← closure_singleton]
    exact isClosed_closure }
  have s2 :  IsOpen (f⁻¹'  u) := IsOpen.preimage hf s1
  have u3 : b ∈ (f⁻¹'  u) := isUpperSet_iff_forall_le.mp s2.1 hab u2
  have c1 : f b ∈ (Iic (f b))ᶜ := by
    simp only [mem_compl_iff, mem_preimage, mem_Iic, le_refl, not_true] at u3
  simp only [mem_compl_iff, mem_Iic, le_refl, not_true] at c1

end WithScottTopology

lemma ScottContinuous_iff_continuous_wrt_Scott
  (f : (WithScottTopology α) → (WithScottTopology β)) :
  ScottContinuous f ↔ Continuous f := by
  constructor
  . intro h
    rw [continuous_def]
    intros u hu
    rw [WithScottTopology.isOpen_iff_upper_and_LUB_mem_implies_inter_nonempty]
    constructor
    . apply IsUpperSet.preimage (WithScottTopology.isOpen_isUpper hu)
      apply ScottContinuous.monotone
      exact h
    . intros d a hd₁ hd₂ hd₃ ha
      have e1: IsLUB (f '' d) (f a) := by
        apply h
        apply hd₁
        apply hd₂
        apply hd₃
      rw [WithScottTopology.isOpen_iff_upper_and_LUB_mem_implies_inter_nonempty] at hu
      have e2: ((f '' d) ∩ u).Nonempty := by
        apply hu.2
        exact Nonempty.image f hd₁
        have e3: Monotone f := by
          apply ScottContinuous.monotone
          exact h
        apply directedOn_image.mpr
        apply DirectedOn.mono hd₂
        apply e3
        apply e1
        exact ha
      exact image_inter_nonempty_iff.mp e2
  . intros hf d d₁ d₂ a d₃
    rw [IsLUB]
    constructor
    . apply Monotone.mem_upperBounds_image (WithScottTopology.continuous_monotone hf)
      rw [← isLUB_le_iff]
      exact d₃
    . rw [lowerBounds, mem_setOf_eq]
      intros b hb
      let u := (Iic b)ᶜ
      by_contra h
      have e1: a ∈ (f⁻¹'  u) := h
      have s1 : IsOpen u := by
        rw [isOpen_compl_iff, ← WithScottTopology.closure_singleton]
        exact isClosed_closure
      have s2 : IsOpen (f⁻¹'  u) := IsOpen.preimage hf s1
      rw [WithScottTopology.isOpen_iff_upper_and_LUB_mem_implies_inter_nonempty] at s2
      obtain ⟨c, ⟨h_1_left, h_1_right⟩⟩ := s2.2 d a d₁ d₂ d₃ e1
      simp at h_1_right
      rw [upperBounds] at hb
      simp at hb
      have c1: f c ≤ b := by
        apply hb
        exact h_1_left
      contradiction

end preorder

section partial_order
variable [PartialOrder α]

instance : PartialOrder (WithScottTopology α) := ‹PartialOrder α›

/--
The Scott topology on a partial order is T₀.
-/
-- see Note [lower instance priority]
instance (priority := 90): T0Space (WithScottTopology α) :=
(t0Space_iff_inseparable (WithScottTopology α)).2 $ fun x y h => Iic_injective $
  by simpa only [inseparable_iff_closure_eq, WithScottTopology.closure_singleton] using h

end partial_order

section complete_lattice

lemma isOpen_eq_upper_and_sup_mem_implies_tail_subset [CompleteLattice α]
(u : Set (WithScottTopology α)) : IsOpen u =
(IsUpperSet u ∧
  ∀ (d : Set α), d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ u → ∃ b ∈ d, (Ici b) ∩ d ⊆ u) := by
  rw [WithScottTopology.isOpen_eq_upper_and_LUB_mem_implies_tail_subset]
  refine' let_value_eq (And (IsUpperSet u)) _
  rw [eq_iff_iff]
  constructor
  . intros h d hd₁ hd₂ hd₃
    exact h d (sSup d) hd₁ hd₂ (isLUB_sSup d) hd₃
  . intros h d a hd₁ hd₂ hd₃ ha
    apply h d hd₁ hd₂
    rw [(IsLUB.sSup_eq hd₃)]
    exact ha

lemma isOpen_eq_upper_and_sup_mem_implies_inter_nonempty [CompleteLattice α]
(u : Set (WithScottTopology α)) : IsOpen u =
(IsUpperSet u ∧  ∀ (d : Set α), d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ u →
(d∩u).Nonempty) := by
  rw [WithScottTopology.isOpen_iff_upper_and_LUB_mem_implies_inter_nonempty]
  refine' let_value_eq (And (IsUpperSet u)) _
  rw [eq_iff_iff]
  constructor
  . intros h d hd₁ hd₂ hd₃
    exact h d (sSup d) hd₁ hd₂ (isLUB_sSup d) hd₃
  . intros h d a hd₁ hd₂ hd₃ ha
    apply h d hd₁ hd₂
    rw [(IsLUB.sSup_eq hd₃)]
    exact ha

end complete_lattice