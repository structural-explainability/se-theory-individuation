module

public import SE.Individuation.Structural.Connectivity
public import SE.Persistence.Commitment.Consistency
public import SE.Persistence.Commitment.Status
public import SE.Persistence.Commitment.Compare

set_option autoImplicit false

/-!
# Persistence Connection: Whole Co-membership Constraints

SE.Individuation.Structural.BoundaryCompatibility

A second use of Persistence's generic commitment calculus operates on eligible atoms.
For the connectivity instance:

- `P` is the bond relation, read as same-whole co-membership commitments;
- `D` is independently warranted commitments that two atoms belong to different wholes.

`D` does not mean that two atoms are unequal. Different atoms can belong to the same whole.
The generated equivalence is whole co-membership, not strict identity of atoms.

This module proves that `BondClosure` agrees with Persistence's `Generated` at universe 0,
so Persistence's results apply: the finite-path characterization, consistency as
compatibility with separation commitments, forbidden proposed bonds, and the
generator-comparison witness.

A rejecting result identifies disagreement among the proposed bonds and independently
warranted boundaries. Determining which input is defective needs further investigation.
A witness localizes a difference. It does not identify a scientifically erroneous bond.

Comparisons across eligible domains need an explicit common carrier or transport.
Inclusion of atoms alone does not establish preservation or reflection of connectivity.
-/

namespace SE.Individuation.Structural

@[expose] public section

open SE.Persistence

variable {C : Type}

/-- `BondClosure` is Persistence's `Generated` at universe 0. -/
theorem bondClosure_iff_generated {r : C → C → Prop} {x y : C} :
    BondClosure r x y ↔ Generated r x y := by
  constructor
  · intro h
    induction h with
    | rel hxy => exact Generated.rel hxy
    | refl x => exact Generated.refl x
    | symm _ ih => exact Generated.symm ih
    | trans _ _ ih1 ih2 => exact Generated.trans ih1 ih2
  · intro h
    induction h with
    | rel hxy => exact BondClosure.rel hxy
    | refl x => exact BondClosure.refl x
    | symm _ ih => exact BondClosure.symm ih
    | trans _ _ ih1 ih2 => exact BondClosure.trans ih1 ih2

/-- Finite-path characterization: bonded atoms are co-members exactly when a finite chain of
bonds, each used in either direction, connects them. The chain explains the co-membership. -/
theorem bondClosure_iff_reach_symmStep {r : C → C → Prop} {x y : C} :
    BondClosure r x y ↔ Reach (SymmStep r) x y :=
  bondClosure_iff_generated.trans generated_iff_reach_symmStep

/-- Boundary compatibility: bonds and separation commitments are consistent exactly when
no pair asserted to be in different wholes lies in the generated co-membership. -/
theorem consistent_iff_no_separated_connected {P D : C → C → Prop} :
    Consistent P D ↔ ∀ x y, D x y → ¬ BondClosure P x y := by
  constructor
  · intro h x y hd hc
    exact h x y hd (bondClosure_iff_generated.1 hc)
  · intro h x y hd hg
    exact h x y hd (bondClosure_iff_generated.2 hg)

/-- A forbidden proposed bond is one whose addition would connect a prohibited pair. -/
theorem forbidden_iff_extend_connects {P D : C → C → Prop} {x y : C} :
    Forbidden P D x y ↔ ∃ u v, D u v ∧ BondClosure (Extend P x y) u v := by
  constructor
  · rintro ⟨u, v, hd, hg⟩
    exact ⟨u, v, hd, bondClosure_iff_generated.2 hg⟩
  · rintro ⟨u, v, hd, hc⟩
    exact ⟨u, v, hd, bondClosure_iff_generated.1 hc⟩

/-- Generator-comparison witness: if two bond sets generate different co-membership relations,
a single bond on one side has endpoints not connected on the other. -/
theorem exists_bond_difference {P Q : C → C → Prop}
    (h : ¬ ∀ x y, BondClosure P x y ↔ BondClosure Q x y) :
    ∃ x y, (P x y ∧ ¬ BondClosure Q x y) ∨ (Q x y ∧ ¬ BondClosure P x y) := by
  have h' : ¬ (GeneratedLE P Q ∧ GeneratedLE Q P) := by
    rintro ⟨h1, h2⟩
    apply h
    intro x y
    constructor
    · intro hb
      exact bondClosure_iff_generated.2 (h1 x y (bondClosure_iff_generated.1 hb))
    · intro hb
      exact bondClosure_iff_generated.2 (h2 x y (bondClosure_iff_generated.1 hb))
  obtain ⟨x, y, hxy⟩ := exists_generator_difference h'
  refine ⟨x, y, ?_⟩
  rcases hxy with ⟨hp, hq⟩ | ⟨hq, hp⟩
  · exact Or.inl ⟨hp, fun hc => hq (bondClosure_iff_generated.1 hc)⟩
  · exact Or.inr ⟨hq, fun hc => hp (bondClosure_iff_generated.1 hc)⟩

namespace Setting

variable {A Presentation : Type}

/-- Consistent bonds and separation commitments make the setting's co-membership admissible. -/
theorem BondGenerated.admissible_of_consistent {s : Setting A Presentation}
    {bond : {a : A // a ∈ s.eligible} → {a : A // a ∈ s.eligible} → Prop}
    (hs : s.BondGenerated bond)
    {D : {a : A // a ∈ s.eligible} → {a : A // a ∈ s.eligible} → Prop}
    (h : Consistent bond D) : Admissible bond D s.E := by
  refine ⟨s.E_equivalence, ?_, ?_⟩
  · intro x y hb
    exact (hs x y).2 (BondClosure.rel hb)
  · intro x y hd hE
    exact (consistent_iff_no_separated_connected.1 h) x y hd ((hs x y).1 hE)

end Setting

end

end SE.Individuation.Structural
