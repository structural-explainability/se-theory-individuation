module

public import Mathlib.Data.Set.Defs

set_option autoImplicit false

/-!
# Structural Setting

SE.Individuation.Structural.Setting

A setting for the exclusive-whole construction at a fixed granularity.
It supplies, for atoms `A` and candidate presentations `Presentation`:

- an eligible domain `eligible ⊆ A`;
- a presentation-admissibility predicate `admissible`;
- a support function `support : Presentation → Set A`;
- containment of admissible supports in `eligible`;
- an equivalence relation `E` on the subtype of eligible atoms.

`E` is whole co-membership under the proposed criterion. It is not equality or
strict identity of atoms.

`Setting.CoMember` lifts `E` to all atoms. It holds only between eligible atoms.
-/

namespace SE.Individuation.Structural

universe u

@[expose] public section

/-- A structural setting: eligible atoms, admissibility, support, and whole co-membership. -/
structure Setting (A : Type u) (Presentation : Type u) where
  /-- The eligible domain: atoms inside the selected boundary. -/
  eligible : Set A
  /-- Eligibility of a candidate presentation for individuation evaluation. -/
  admissible : Presentation → Prop
  /-- The atoms represented by a presentation at this setting. -/
  support : Presentation → Set A
  /-- Admissible supports lie inside the eligible domain. -/
  support_subset_eligible : ∀ p, admissible p → support p ⊆ eligible
  /-- Whole co-membership on eligible atoms. -/
  E : {a : A // a ∈ eligible} → {a : A // a ∈ eligible} → Prop
  /-- Whole co-membership is an equivalence relation on eligible atoms. -/
  E_equivalence : Equivalence E

namespace Setting

variable {A Presentation : Type u}

/-- Whole co-membership lifted to all atoms: both atoms are eligible and `E`-related. -/
def CoMember (s : Setting A Presentation) (a b : A) : Prop :=
  ∃ (ha : a ∈ s.eligible) (hb : b ∈ s.eligible), s.E ⟨a, ha⟩ ⟨b, hb⟩

/-- The left element of a co-member pair is eligible. -/
theorem CoMember.left_eligible {s : Setting A Presentation} {a b : A}
    (h : s.CoMember a b) : a ∈ s.eligible := by
  obtain ⟨ha, _, _⟩ := h
  exact ha

/-- The right element of a co-member pair is eligible. -/
theorem CoMember.right_eligible {s : Setting A Presentation} {a b : A}
    (h : s.CoMember a b) : b ∈ s.eligible := by
  obtain ⟨_, hb, _⟩ := h
  exact hb

/-- Co-membership is reflexive on eligible atoms. -/
theorem CoMember.refl {s : Setting A Presentation} {a : A}
    (ha : a ∈ s.eligible) : s.CoMember a a :=
  ⟨ha, ha, s.E_equivalence.refl ⟨a, ha⟩⟩

/-- Co-membership is symmetric. -/
theorem CoMember.symm {s : Setting A Presentation} {a b : A}
    (h : s.CoMember a b) : s.CoMember b a := by
  obtain ⟨ha, hb, hab⟩ := h
  exact ⟨hb, ha, s.E_equivalence.symm hab⟩

/-- Co-membership is transitive. -/
theorem CoMember.trans {s : Setting A Presentation} {a b c : A}
    (h1 : s.CoMember a b) (h2 : s.CoMember b c) : s.CoMember a c := by
  obtain ⟨ha, hb, hab⟩ := h1
  obtain ⟨hb', hc, hbc⟩ := h2
  exact ⟨ha, hc, s.E_equivalence.trans hab hbc⟩

/-- Co-membership of eligible atoms is `E` on the corresponding subtype elements. -/
theorem CoMember.to_E {s : Setting A Presentation} {a b : A}
    (h : s.CoMember a b) (ha : a ∈ s.eligible) (hb : b ∈ s.eligible) :
    s.E ⟨a, ha⟩ ⟨b, hb⟩ := by
  obtain ⟨_, _, hab⟩ := h
  exact hab

/-- `E` on subtype elements gives co-membership of their underlying atoms. -/
theorem CoMember.of_E {s : Setting A Presentation}
    {x y : {a : A // a ∈ s.eligible}} (h : s.E x y) : s.CoMember x.1 y.1 :=
  ⟨x.2, y.2, h⟩

end Setting

end

end SE.Individuation.Structural
