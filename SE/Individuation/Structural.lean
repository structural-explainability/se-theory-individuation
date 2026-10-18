import SE.Individuation

set_option autoImplicit false

/-!
# Finite Witnesses and Essential-Hypothesis Counterexamples

SETest.Individuation.Structural

Small settings over `Bool` atoms and `Nat` atoms. These witness the construction checks
of the contract; they do not ground the criterion in any kind of whole.
-/

namespace SETest.Individuation.Structural

open SE.Individuation.Structural

/-! ### Elementary set facts used below -/

theorem mem_univ' {α : Type} (a : α) : a ∈ (Set.univ : Set α) := trivial

theorem mem_singleton' {α : Type} (a : α) : a ∈ ({a} : Set α) := rfl

theorem mem_singleton_iff' {α : Type} {a b : α} : a ∈ ({b} : Set α) ↔ a = b := Iff.rfl

theorem notMem_empty' {α : Type} (a : α) : a ∉ (∅ : Set α) := fun h => h

/-- With no bonds, the generated relation is equality. -/
theorem eq_of_no_bonds {C : Type} {r : C → C → Prop} (hr : ∀ x y, ¬ r x y) {x y : C}
    (h : BondClosure r x y) : x = y := by
  induction h with
  | rel hxy => exact absurd hxy (hr _ _)
  | refl x => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Two atoms, no bonds. Presentations are labelled sets of atoms; support forgets the label. -/
def noBonds : Setting Bool (Set Bool × Nat) :=
  Setting.ofBonds Set.univ (fun _ => True) (fun p => p.1)
    (by intro p _ a _; exact mem_univ' a) (fun _ _ => False)

/-- Two atoms joined by a bond. -/
def linked : Setting Bool (Set Bool × Nat) :=
  Setting.ofBonds Set.univ (fun _ => True) (fun p => p.1)
    (by intro p _ a _; exact mem_univ' a) (fun _ _ => True)

/-! ### Construction checks -/

/-- 1. Empty support fails nonemptiness. -/
theorem empty_support_fails : ¬ noBonds.WholeConditions (∅ : Set Bool) := by
  rintro ⟨⟨a, ha, _⟩, _, _⟩
  exact notMem_empty' a ha

/-- 2. A disconnected aggregate fails internal co-membership. -/
theorem disconnected_aggregate_fails : ¬ noBonds.WholeConditions (Set.univ : Set Bool) := by
  rintro ⟨_, hint, _⟩
  obtain ⟨_, _, h⟩ := hint true false (mem_univ' _) (mem_univ' _)
  have heq := eq_of_no_bonds (fun _ _ hf => hf) h
  have h2 : true = false := congrArg Subtype.val heq
  cases h2

/-- 3. A proper connected part fails saturation. -/
theorem connected_part_fails_saturation : ¬ linked.WholeConditions ({true} : Set Bool) := by
  rintro ⟨_, _, hsat⟩
  have hco : linked.CoMember true false :=
    ⟨mem_univ' _, mem_univ' _, BondClosure.rel trivial⟩
  have hf : false ∈ ({true} : Set Bool) :=
    hsat true false (mem_singleton' true) (mem_univ' _) hco
  have h2 : false = true := mem_singleton_iff'.1 hf
  cases h2

theorem linked_univ_whole : linked.WholeConditions (Set.univ : Set Bool) := by
  refine ⟨⟨true, mem_univ' _, mem_univ' _⟩, ?_, ?_⟩
  · intro a b _ _
    exact ⟨mem_univ' _, mem_univ' _, BondClosure.rel trivial⟩
  · intro a b _ _ _
    exact mem_univ' _

/-- 4. Different successful presentations of one support identify one unit. -/
theorem relabelled_presentations_same_unit :
    linked.SameUnit (Set.univ, 0) (Set.univ, 1) :=
  ⟨⟨trivial, linked_univ_whole⟩, ⟨trivial, linked_univ_whole⟩, rfl⟩

theorem noBonds_singleton_whole (a : Bool) : noBonds.WholeConditions ({a} : Set Bool) := by
  refine Setting.wholeConditions_singleton_of_isolated (mem_univ' a) ?_
  intro b hab
  obtain ⟨_, _, h⟩ := hab
  have heq := eq_of_no_bonds (fun _ _ hf => hf) h
  exact (congrArg Subtype.val heq).symm

/-- 5. Disconnected isomorphic copies remain distinct. -/
theorem isolated_copies_distinct :
    noBonds.DistinctUnits ({true}, 0) ({false}, 0) ∧
      ¬ noBonds.SameUnit ({true}, 0) ({false}, 0) := by
  have hp : noBonds.Succeeds ({true}, 0) := ⟨trivial, noBonds_singleton_whole true⟩
  have hq : noBonds.Succeeds ({false}, 0) := ⟨trivial, noBonds_singleton_whole false⟩
  have hd : noBonds.DistinctUnits ({true}, 0) ({false}, 0) := by
    refine ⟨hp, hq, ?_⟩
    intro a ha hb
    have ha' : a = true := mem_singleton_iff'.1 ha
    have hb' : a = false := mem_singleton_iff'.1 hb
    rw [ha'] at hb'
    cases hb'
  exact ⟨hd, (Setting.distinctUnits_iff_not_sameUnit hp hq).1 hd⟩

/-- 6. Overlap of arbitrary subsets does not establish successful-whole identity:
the success hypotheses of the overlap characterization are essential. -/
theorem overlap_without_success :
    ∃ p q, (∃ a, a ∈ linked.support p ∧ a ∈ linked.support q) ∧ ¬ linked.SameUnit p q := by
  refine ⟨({true}, 0), (Set.univ, 0), ⟨true, mem_singleton' true, mem_univ' _⟩, ?_⟩
  intro h
  exact connected_part_fails_saturation h.1.2

/-- Why nonemptiness is needed for the dichotomy: empty sets are both equal and disjoint. -/
theorem empty_sets_equal_and_disjoint :
    (∅ : Set Bool) = ∅ ∧ ∀ a, a ∈ (∅ : Set Bool) → a ∉ (∅ : Set Bool) :=
  ⟨rfl, fun a ha _ => notMem_empty' a ha⟩

/-- Without a presentation-coverage condition, a whole can exist with no presentation (check 7). -/
def uncovered : Setting Bool Empty :=
  Setting.ofBonds Set.univ (fun _ => False) (fun p => p.elim)
    (by intro p; exact p.elim) (fun _ _ => True)

theorem class_without_presentation :
    (∃ W, uncovered.IsClass W) ∧ ∀ p : Empty, ¬ uncovered.Succeeds p := by
  refine ⟨⟨Set.univ, true, mem_univ' _, fun b => ⟨fun _ => ?_, fun _ => mem_univ' _⟩⟩,
    fun p => p.elim⟩
  exact ⟨mem_univ' _, mem_univ' _, BondClosure.rel trivial⟩

/-! ### Boundary compatibility (rejection) -/

/-- Bonds joining two atoms are incompatible with a warranted separation of those atoms. -/
theorem boundary_incompatible :
    ¬ SE.Persistence.Consistent
      (fun (_ _ : {a : Bool // a ∈ (Set.univ : Set Bool)}) => True)
      (fun x y => x.1 = true ∧ y.1 = false) := by
  intro h
  exact (consistent_iff_no_separated_connected.1 h)
    ⟨true, mem_univ' _⟩ ⟨false, mem_univ' _⟩ ⟨rfl, rfl⟩ (BondClosure.rel trivial)

/-! ### Changing boundaries -/

/-- Atoms `0 ≤ n ≤ 2`, each bonded to its successor. -/
def fullBond (x y : {n : Nat // n ≤ 2}) : Prop := x.1 + 1 = y.1

/-- The same bond rule on the boundary that excludes atom `1`. -/
def reducedBond (x y : {n : Nat // n = 0 ∨ n = 2}) : Prop := x.1 + 1 = y.1

/-- Atoms 0 and 2 are connected through atom 1 in the full boundary. -/
theorem full_boundary_connects :
    BondClosure fullBond (⟨0, by omega⟩ : {n : Nat // n ≤ 2}) ⟨2, by omega⟩ :=
  BondClosure.trans
    (BondClosure.rel (show fullBond ⟨0, by omega⟩ ⟨1, by omega⟩ from rfl))
    (BondClosure.rel (show fullBond ⟨1, by omega⟩ ⟨2, by omega⟩ from rfl))

/-- Excluding atom 1 removes the connecting path, though atoms 0 and 2 are still eligible.
Inclusion of atoms alone does not establish preservation of connectivity. -/
theorem reduced_boundary_disconnects :
    ¬ BondClosure reducedBond (⟨0, Or.inl rfl⟩ : {n : Nat // n = 0 ∨ n = 2}) ⟨2, Or.inr rfl⟩ := by
  intro h
  have hno : ∀ x y : {n : Nat // n = 0 ∨ n = 2}, ¬ reducedBond x y := by
    intro x y hxy
    unfold reducedBond at hxy
    have hx := x.2
    have hy := y.2
    omega
  have heq := eq_of_no_bonds hno h
  have h2 : (0 : Nat) = 2 := congrArg Subtype.val heq
  cases h2

end SETest.Individuation.Structural
