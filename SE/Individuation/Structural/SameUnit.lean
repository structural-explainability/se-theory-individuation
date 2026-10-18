module

public import SE.Individuation.Structural.Whole

set_option autoImplicit false

/-!
# Same-Unit and Distinct-Unit Judgments

SE.Individuation.Structural.SameUnit

Two presentations identify the same unit exactly when both succeed and their
supports are equal. They identify distinct units exactly when both succeed and
their supports share no atom.

Both are guarded by success. Same-unit identity is an equivalence relation on
successful presentations only; its extension to all candidate presentations is
not globally reflexive (`not_sameUnit_refl_of_not_succeeds`).

The mathematical complement of same-unit on successful presentations is
distinctness (`distinctUnits_iff_not_sameUnit`). This does not justify treating
failure to establish sameness from evidence as established distinctness.

This construction is exclusive-whole and extensional. Neither commitment is a
requirement of Individuation in general.
-/

namespace SE.Individuation.Structural

universe u

@[expose] public section

namespace Setting

variable {A Presentation : Type u}

/-- Both presentations succeed and their supports are equal. -/
def SameUnit (s : Setting A Presentation) (p q : Presentation) : Prop :=
  s.Succeeds p ∧ s.Succeeds q ∧ s.support p = s.support q

/-- Both presentations succeed and their supports share no atom. -/
def DistinctUnits (s : Setting A Presentation) (p q : Presentation) : Prop :=
  s.Succeeds p ∧ s.Succeeds q ∧ ∀ a, a ∈ s.support p → a ∉ s.support q

/-- `SameUnit` is symmetric. -/
theorem SameUnit.symm {s : Setting A Presentation} {p q : Presentation}
    (h : s.SameUnit p q) : s.SameUnit q p :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

/-- `SameUnit` is transitive. -/
theorem SameUnit.trans {s : Setting A Presentation} {p q r : Presentation}
    (h1 : s.SameUnit p q) (h2 : s.SameUnit q r) : s.SameUnit p r :=
  ⟨h1.1, h2.2.1, h1.2.2.trans h2.2.2⟩

/-- Same-unit identity at `p` with itself is exactly success of `p`. -/
theorem sameUnit_refl_iff (s : Setting A Presentation) (p : Presentation) :
    s.SameUnit p p ↔ s.Succeeds p :=
  ⟨fun h => h.1, fun h => ⟨h, h, rfl⟩⟩

/-- Same-unit identity is an equivalence relation on the subtype of successful presentations. -/
theorem sameUnit_equivalence (s : Setting A Presentation) :
    Equivalence (fun x y : {p : Presentation // s.Succeeds p} => s.SameUnit x.1 y.1) :=
  ⟨fun x => ⟨x.2, x.2, rfl⟩, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- The success-guarded relation is not reflexive at a presentation that fails. -/
theorem not_sameUnit_refl_of_not_succeeds {s : Setting A Presentation} {p : Presentation}
    (h : ¬ s.Succeeds p) : ¬ s.SameUnit p p :=
  fun hs => h hs.1

/-- Overlap characterization: on successful presentations, same unit is exactly overlap of supports.
The success hypotheses are essential. -/
theorem sameUnit_iff_overlap {s : Setting A Presentation} {p q : Presentation}
    (hp : s.Succeeds p) (hq : s.Succeeds q) :
    s.SameUnit p q ↔ ∃ a, a ∈ s.support p ∧ a ∈ s.support q := by
  constructor
  · rintro ⟨_, _, heq⟩
    obtain ⟨a, ha, _⟩ := hp.2.1
    refine ⟨a, ha, ?_⟩
    rw [← heq]
    exact ha
  · rintro ⟨a, h1, h2⟩
    rcases hp.2.eq_or_disjoint hq.2 with heq | hdis
    · exact ⟨hp, hq, heq⟩
    · exact absurd h2 (hdis a h1)

/-- Same-or-distinct dichotomy on successful presentations: at least one holds. -/
theorem sameUnit_or_distinctUnits {s : Setting A Presentation} {p q : Presentation}
    (hp : s.Succeeds p) (hq : s.Succeeds q) :
    s.SameUnit p q ∨ s.DistinctUnits p q := by
  rcases hp.2.eq_or_disjoint hq.2 with heq | hdis
  · exact Or.inl ⟨hp, hq, heq⟩
  · exact Or.inr ⟨hp, hq, hdis⟩

/-- Same-or-distinct dichotomy on successful presentations: not both. -/
theorem not_sameUnit_and_distinctUnits {s : Setting A Presentation} {p q : Presentation}
    (hp : s.Succeeds p) :
    ¬ (s.SameUnit p q ∧ s.DistinctUnits p q) := by
  rintro ⟨⟨_, _, heq⟩, ⟨_, _, hdis⟩⟩
  exact hp.2.not_eq_and_disjoint ⟨heq, hdis⟩

/-- On successful presentations, distinct units is exactly failure of same unit. -/
theorem distinctUnits_iff_not_sameUnit {s : Setting A Presentation} {p q : Presentation}
    (hp : s.Succeeds p) (hq : s.Succeeds q) :
    s.DistinctUnits p q ↔ ¬ s.SameUnit p q := by
  constructor
  · intro hd hs
    exact not_sameUnit_and_distinctUnits hp ⟨hs, hd⟩
  · intro hns
    rcases sameUnit_or_distinctUnits hp hq with hs | hd
    · exact absurd hs hns
    · exact hd

/-- Lossless re-presentation: admissible presentations with equal supports have the same success status. -/
theorem succeeds_iff_of_support_eq {s : Setting A Presentation} {p q : Presentation}
    (hp : s.admissible p) (hq : s.admissible q) (h : s.support p = s.support q) :
    s.Succeeds p ↔ s.Succeeds q := by
  constructor
  · rintro ⟨_, hw⟩
    refine ⟨hq, ?_⟩
    rw [← h]
    exact hw
  · rintro ⟨_, hw⟩
    refine ⟨hp, ?_⟩
    rw [h]
    exact hw

/-- Lossless re-presentation: when one succeeds, an admissible presentation with equal support
identifies the same unit, whatever its format, labels, or annotation. -/
theorem sameUnit_of_support_eq {s : Setting A Presentation} {p q : Presentation}
    (hp : s.Succeeds p) (hq : s.admissible q) (h : s.support p = s.support q) :
    s.SameUnit p q :=
  ⟨hp, (succeeds_iff_of_support_eq hp.1 hq h).1 hp, h⟩

end Setting

end

end SE.Individuation.Structural
