module

public import SE.Individuation.Structural.SameUnit
public import SE.Persistence.Commitment.Observed

set_option autoImplicit false

/-!
# Persistence Connection: Successful Presentations

SE.Individuation.Structural.Commitments

At a setting, the carrier is the subtype of successful presentations. With

- `P` the same-unit judgments,
- `D` the distinct-unit judgments,
- `E` support equality,

this module proves, using Persistence's commitment calculus:

- `E` is Persistence-admissible for `P` and `D`;
- the commitments are consistent;
- `E` is the unique admissible relation;
- no pair is undetermined under these exact commitments;
- `D` coincides with the pairs separated by the support observation map.

Hypotheses used: nonemptiness of successful supports, and the same-or-distinct dichotomy
(for uniqueness and for unequal implies disjoint). The coincidence of `D` with the
separated pairs depends on exclusivity through the dichotomy.

This is a soundness construction and establishes mathematical correctness only. One
criterion determines both `P` and `D`, so consistency does not independently validate
the criterion against practice.

Persistence's calculus is stated for carriers in `Type`, so this module specializes
atoms and presentations to universe 0.
-/

namespace SE.Individuation.Structural

@[expose] public section

open SE.Persistence

namespace Setting

variable {A Presentation : Type} (s : Setting A Presentation)

/-- Same-unit judgments on successful presentations. -/
def samePairs : {p : Presentation // s.Succeeds p} → {p : Presentation // s.Succeeds p} → Prop :=
  fun x y => s.SameUnit x.1 y.1

/-- Distinct-unit judgments on successful presentations. -/
def distinctPairs :
    {p : Presentation // s.Succeeds p} → {p : Presentation // s.Succeeds p} → Prop :=
  fun x y => s.DistinctUnits x.1 y.1

/-- Support equality on successful presentations. -/
def supportEquality :
    {p : Presentation // s.Succeeds p} → {p : Presentation // s.Succeeds p} → Prop :=
  fun x y => s.support x.1 = s.support y.1

/-- The support observation map on successful presentations. -/
def supportObservation : {p : Presentation // s.Succeeds p} → Set A :=
  fun x => s.support x.1

/-- Equality of support is an equivalence relation. -/
theorem supportEquality_equivalence : Equivalence s.supportEquality :=
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- Support equality is Persistence-admissible for same-unit and distinct-unit judgments. -/
theorem supportEquality_admissible :
    Admissible s.samePairs s.distinctPairs s.supportEquality := by
  refine ⟨s.supportEquality_equivalence, ?_, ?_⟩
  · intro x y h
    exact h.2.2
  · intro x y hd heq
    obtain ⟨a, ha, _⟩ := x.2.2.1
    apply hd.2.2 a ha
    have heq' : s.support x.1 = s.support y.1 := heq
    rw [← heq']
    exact ha

/-- The same-unit and distinct-unit commitments are consistent. -/
theorem commitments_consistent : Consistent s.samePairs s.distinctPairs :=
  consistent_of_admissible s.supportEquality_admissible

/-- Support equality is the only admissible relation. Uses the same-or-distinct dichotomy. -/
theorem supportEquality_unique {E : {p : Presentation // s.Succeeds p} →
      {p : Presentation // s.Succeeds p} → Prop}
    (hE : Admissible s.samePairs s.distinctPairs E) (x y : {p : Presentation // s.Succeeds p}) :
    E x y ↔ s.supportEquality x y := by
  constructor
  · intro hxy
    rcases Setting.sameUnit_or_distinctUnits x.2 y.2 with hs | hd
    · exact hs.2.2
    · exact absurd hxy (hE.2.2 x y hd)
  · intro heq
    exact hE.2.1 x y ⟨x.2, y.2, heq⟩

/-- No pair of successful presentations is undetermined under these exact commitments. -/
theorem no_undetermined (x y : {p : Presentation // s.Succeeds p}) :
    ¬ Undetermined s.samePairs s.distinctPairs x y := by
  rintro ⟨hnr, hnf⟩
  rcases Setting.sameUnit_or_distinctUnits x.2 y.2 with hs | hd
  · exact hnr (Generated.rel hs)
  · exact hnf (forbidden_of_distinct hd)

/-- The distinct-unit commitments coincide with the pairs separated by the support observation map. -/
theorem distinctPairs_iff_separated (x y : {p : Presentation // s.Succeeds p}) :
    s.distinctPairs x y ↔ SeparatedBy s.supportObservation x y := by
  constructor
  · intro hd heq
    exact s.supportEquality_admissible.2.2 x y hd heq
  · intro hsep
    rcases Setting.sameUnit_or_distinctUnits x.2 y.2 with hs | hd
    · exact absurd hs.2.2 hsep
    · exact hd

end Setting

end

end SE.Individuation.Structural
