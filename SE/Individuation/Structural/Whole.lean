module

public import SE.Individuation.Structural.Setting

set_option autoImplicit false

/-!
# Whole Conditions and Characterization

SE.Individuation.Structural.Whole

An admissible presentation with support `W` succeeds exactly when:

1. nonemptiness: `W` contains an eligible atom;
2. internal co-membership: every two atoms in `W` are co-members;
3. saturation: every eligible atom co-member with an atom in `W` is in `W`.

These conditions characterize exactly one `E`-class of eligible atoms
(`wholeConditions_iff_isClass`). The result uses only the equivalence-class
structure of `E`, not the connectivity construction.
-/

namespace SE.Individuation.Structural

universe u

@[expose] public section

namespace Setting

variable {A Presentation : Type u}

/-- The three whole conditions on a set of atoms. -/
def WholeConditions (s : Setting A Presentation) (W : Set A) : Prop :=
  (∃ a, a ∈ W ∧ a ∈ s.eligible) ∧
  (∀ a b, a ∈ W → b ∈ W → s.CoMember a b) ∧
  (∀ a b, a ∈ W → b ∈ s.eligible → s.CoMember a b → b ∈ W)

/-- A presentation succeeds when it is admissible and its support meets the whole conditions. -/
def Succeeds (s : Setting A Presentation) (p : Presentation) : Prop :=
  s.admissible p ∧ s.WholeConditions (s.support p)

/-- `W` is the `E`-class of some eligible atom. -/
def IsClass (s : Setting A Presentation) (W : Set A) : Prop :=
  ∃ a, a ∈ s.eligible ∧ ∀ b, b ∈ W ↔ s.CoMember a b

/-- The whole conditions characterize exactly one eligible `E`-class. -/
theorem wholeConditions_iff_isClass (s : Setting A Presentation) (W : Set A) :
    s.WholeConditions W ↔ s.IsClass W := by
  constructor
  · rintro ⟨⟨a, haW, hae⟩, hint, hsat⟩
    refine ⟨a, hae, fun b => ⟨fun hb => hint a b haW hb, fun hab => ?_⟩⟩
    exact hsat a b haW hab.right_eligible hab
  · rintro ⟨a, hae, hW⟩
    refine ⟨⟨a, (hW a).2 (CoMember.refl hae), hae⟩, ?_, ?_⟩
    · intro b c hb hc
      exact ((hW b).1 hb).symm.trans ((hW c).1 hc)
    · intro b c hb _ hbc
      exact (hW c).2 (((hW b).1 hb).trans hbc)

/-- Every set meeting the whole conditions lies inside the eligible domain. -/
theorem WholeConditions.subset_eligible {s : Setting A Presentation} {W : Set A}
    (h : s.WholeConditions W) : W ⊆ s.eligible := by
  intro a ha
  exact (h.2.1 a a ha ha).left_eligible

/-- Success of an admissible presentation is exactly that its support is one eligible class. -/
theorem succeeds_iff_isClass (s : Setting A Presentation) (p : Presentation) :
    s.Succeeds p ↔ s.admissible p ∧ s.IsClass (s.support p) := by
  constructor
  · rintro ⟨hadm, hw⟩
    exact ⟨hadm, (wholeConditions_iff_isClass s _).1 hw⟩
  · rintro ⟨hadm, hc⟩
    exact ⟨hadm, (wholeConditions_iff_isClass s _).2 hc⟩

/-- A presentation that succeeds is admissible. -/
theorem Succeeds.admissible {s : Setting A Presentation} {p : Presentation}
    (h : s.Succeeds p) : s.admissible p := h.1

/-- Two sets meeting the whole conditions are equal or share no atom. -/
theorem WholeConditions.eq_or_disjoint {s : Setting A Presentation} {W₁ W₂ : Set A}
    (h₁ : s.WholeConditions W₁) (h₂ : s.WholeConditions W₂) :
    W₁ = W₂ ∨ ∀ a, a ∈ W₁ → a ∉ W₂ := by
  by_cases h : ∃ a, a ∈ W₁ ∧ a ∈ W₂
  · obtain ⟨a, ha1, ha2⟩ := h
    left
    apply Set.ext
    intro b
    constructor
    · intro hb
      have hab : s.CoMember a b := h₁.2.1 a b ha1 hb
      exact h₂.2.2 a b ha2 hab.right_eligible hab
    · intro hb
      have hab : s.CoMember a b := h₂.2.1 a b ha2 hb
      exact h₁.2.2 a b ha1 hab.right_eligible hab
  · right
    intro a ha1 ha2
    exact h ⟨a, ha1, ha2⟩

/-- Two sets meeting the whole conditions are not both equal and disjoint.
Nonemptiness is what excludes the overlap of the two cases. -/
theorem WholeConditions.not_eq_and_disjoint {s : Setting A Presentation} {W₁ W₂ : Set A}
    (h₁ : s.WholeConditions W₁) :
    ¬ (W₁ = W₂ ∧ ∀ a, a ∈ W₁ → a ∉ W₂) := by
  obtain ⟨⟨a, ha, _⟩, _, _⟩ := h₁
  rintro ⟨heq, hdis⟩
  apply hdis a ha
  rw [← heq]
  exact ha

end Setting

end

end SE.Individuation.Structural
