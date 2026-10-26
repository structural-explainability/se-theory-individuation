/-
Copyright (c) 2026 Denise M. Case. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denise M. Case
-/
module

public import SE.Individuation.Structural.Connectivity
public import SE.Individuation.Structural.SameUnit

set_option autoImplicit false

/-!
# Structural Transport

SE.Individuation.Structural.Transport

A bijection between eligible domains that preserves and reflects whole co-membership
transports whole supports and their equality and disjointness relations. For the
connectivity instance, a bijection that preserves and reflects bonds is sufficient.

Presentation-level transport additionally needs a presentation map that preserves
and reflects admissibility and carries supports to their corresponding images.

These results establish invariance of the construction under the stated transport.
They do not establish strict identity across settings.
-/

namespace SE.Individuation.Structural

universe u v

@[expose] public section

variable {A₁ P₁ : Type u} {A₂ P₂ : Type v}

/-- A bijection between eligible domains preserving and reflecting whole co-membership. -/
structure EligibleIso (s₁ : Setting A₁ P₁) (s₂ : Setting A₂ P₂) where
  /-- The forward map between eligible elements. -/
  toFun : {a : A₁ // a ∈ s₁.eligible} → {b : A₂ // b ∈ s₂.eligible}
  /-- The inverse map between eligible elements. -/
  invFun : {b : A₂ // b ∈ s₂.eligible} → {a : A₁ // a ∈ s₁.eligible}
  /-- `invFun` is a left inverse of `toFun`. -/
  left_inv : ∀ x, invFun (toFun x) = x
  /-- `toFun` is a right inverse of `invFun`. -/
  right_inv : ∀ y, toFun (invFun y) = y
  /-- `toFun` preserves the setting's structure. -/
  preserves : ∀ x y, s₁.E x y → s₂.E (toFun x) (toFun y)
  /-- `toFun` reflects the setting's structure: related images come from related elements. -/
  reflects : ∀ x y, s₂.E (toFun x) (toFun y) → s₁.E x y

namespace EligibleIso

variable {s₁ : Setting A₁ P₁} {s₂ : Setting A₂ P₂}

/-- The image of a set of atoms: images of its eligible atoms. -/
def image (f : EligibleIso s₁ s₂) (W : MathlibMini.Set A₁) : MathlibMini.Set A₂ :=
  fun b => ∃ x : {a : A₁ // a ∈ s₁.eligible}, x.1 ∈ W ∧ (f.toFun x).1 = b

/-- An element lies in the image exactly when it comes from an eligible element. -/
theorem mem_image_iff (f : EligibleIso s₁ s₂) (x : {a : A₁ // a ∈ s₁.eligible}) (W : MathlibMini.Set A₁) :
    (f.toFun x).1 ∈ f.image W ↔ x.1 ∈ W := by
  constructor
  · rintro ⟨x', hx', heq⟩
    have h1 : f.toFun x' = f.toFun x := Subtype.ext heq
    have h2 : x' = x :=
      calc x' = f.invFun (f.toFun x') := (f.left_inv x').symm
        _ = f.invFun (f.toFun x) := by rw [h1]
        _ = x := f.left_inv x
    rw [h2] at hx'
    exact hx'
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Co-membership of eligible atoms is preserved and reflected. -/
theorem coMember_iff (f : EligibleIso s₁ s₂) (a b : A₁)
    (ha : a ∈ s₁.eligible) (hb : b ∈ s₁.eligible) :
    s₁.CoMember a b ↔ s₂.CoMember (f.toFun ⟨a, ha⟩).1 (f.toFun ⟨b, hb⟩).1 := by
  constructor
  · intro h
    exact Setting.CoMember.of_E (f.preserves _ _ (h.to_E ha hb))
  · intro h
    exact Setting.CoMember.of_E
      (f.reflects ⟨a, ha⟩ ⟨b, hb⟩
        (h.to_E (f.toFun ⟨a, ha⟩).2 (f.toFun ⟨b, hb⟩).2))

/-- The whole conditions are invariant under structural transport of sets inside the eligible domain. -/
theorem wholeConditions_image_iff (f : EligibleIso s₁ s₂) {W : MathlibMini.Set A₁}
    (hW : W ⊆ s₁.eligible) :
    s₁.WholeConditions W ↔ s₂.WholeConditions (f.image W) := by
  constructor
  · rintro ⟨⟨a, haW, hae⟩, hint, hsat⟩
    refine ⟨⟨(f.toFun ⟨a, hae⟩).1, (f.mem_image_iff ⟨a, hae⟩ W).2 haW,
      (f.toFun ⟨a, hae⟩).2⟩, ?_, ?_⟩
    · intro b c hb hc
      obtain ⟨x, hx, rfl⟩ := hb
      obtain ⟨y, hy, rfl⟩ := hc
      exact (f.coMember_iff x.1 y.1 x.2 y.2).1 (hint x.1 y.1 hx hy)
    · intro b c hb hc hbc
      obtain ⟨x, hx, rfl⟩ := hb
      have hz : (f.toFun (f.invFun ⟨c, hc⟩)).1 = c :=
        congrArg Subtype.val (f.right_inv ⟨c, hc⟩)
      have hbc' : s₂.CoMember (f.toFun x).1 (f.toFun (f.invFun ⟨c, hc⟩)).1 := by
        rw [hz]
        exact hbc
      have hxz : s₁.CoMember x.1 (f.invFun ⟨c, hc⟩).1 :=
        (f.coMember_iff x.1 (f.invFun ⟨c, hc⟩).1 x.2 (f.invFun ⟨c, hc⟩).2).2 hbc'
      exact ⟨f.invFun ⟨c, hc⟩, hsat x.1 _ hx (f.invFun ⟨c, hc⟩).2 hxz, hz⟩
  · rintro ⟨⟨b, hbi, _⟩, hint₂, hsat₂⟩
    obtain ⟨x, hx, _⟩ := hbi
    refine ⟨⟨x.1, hx, x.2⟩, ?_, ?_⟩
    · intro a c ha hc
      have ha' : (f.toFun ⟨a, hW ha⟩).1 ∈ f.image W := (f.mem_image_iff ⟨a, hW ha⟩ W).2 ha
      have hc' : (f.toFun ⟨c, hW hc⟩).1 ∈ f.image W := (f.mem_image_iff ⟨c, hW hc⟩ W).2 hc
      exact (f.coMember_iff a c (hW ha) (hW hc)).2 (hint₂ _ _ ha' hc')
    · intro a c ha hce hac
      have ha' : (f.toFun ⟨a, hW ha⟩).1 ∈ f.image W := (f.mem_image_iff ⟨a, hW ha⟩ W).2 ha
      have h₂ : s₂.CoMember (f.toFun ⟨a, hW ha⟩).1 (f.toFun ⟨c, hce⟩).1 :=
        (f.coMember_iff a c (hW ha) hce).1 hac
      have hcm : (f.toFun ⟨c, hce⟩).1 ∈ f.image W :=
        hsat₂ _ _ ha' (f.toFun ⟨c, hce⟩).2 h₂
      exact (f.mem_image_iff ⟨c, hce⟩ W).1 hcm

/-- Transport preserves and reflects equality of sets inside the eligible domain. -/
theorem image_eq_iff (f : EligibleIso s₁ s₂) {W₁ W₂ : MathlibMini.Set A₁}
    (h₁ : W₁ ⊆ s₁.eligible) (h₂ : W₂ ⊆ s₁.eligible) :
    f.image W₁ = f.image W₂ ↔ W₁ = W₂ := by
  constructor
  · intro h
    apply MathlibMini.Set.ext
    intro a
    constructor
    · intro ha
      have hm : (f.toFun ⟨a, h₁ ha⟩).1 ∈ f.image W₁ := (f.mem_image_iff ⟨a, h₁ ha⟩ W₁).2 ha
      rw [h] at hm
      exact (f.mem_image_iff ⟨a, h₁ ha⟩ W₂).1 hm
    · intro ha
      have hm : (f.toFun ⟨a, h₂ ha⟩).1 ∈ f.image W₂ := (f.mem_image_iff ⟨a, h₂ ha⟩ W₂).2 ha
      rw [← h] at hm
      exact (f.mem_image_iff ⟨a, h₂ ha⟩ W₁).1 hm
  · intro h
    rw [h]

/-- Transport preserves and reflects disjointness of sets, given the first lies in the eligible domain. -/
theorem image_disjoint_iff (f : EligibleIso s₁ s₂) {W₁ W₂ : MathlibMini.Set A₁}
    (h₁ : W₁ ⊆ s₁.eligible) :
    (∀ b, b ∈ f.image W₁ → b ∉ f.image W₂) ↔ (∀ a, a ∈ W₁ → a ∉ W₂) := by
  constructor
  · intro H a ha ha2
    exact H (f.toFun ⟨a, h₁ ha⟩).1 ((f.mem_image_iff ⟨a, h₁ ha⟩ W₁).2 ha)
      ((f.mem_image_iff ⟨a, h₁ ha⟩ W₂).2 ha2)
  · intro H b hb hb2
    obtain ⟨x, hx, rfl⟩ := hb
    exact H x.1 hx ((f.mem_image_iff x W₂).1 hb2)

/-- For the connectivity instance, a bijection of eligible atoms that preserves and reflects
bonds gives a structural transport. -/
def ofBondCorrespondence {s₁ : Setting A₁ P₁} {s₂ : Setting A₂ P₂}
    {bond₁ : {a : A₁ // a ∈ s₁.eligible} → {a : A₁ // a ∈ s₁.eligible} → Prop}
    {bond₂ : {b : A₂ // b ∈ s₂.eligible} → {b : A₂ // b ∈ s₂.eligible} → Prop}
    (hs₁ : s₁.BondGenerated bond₁) (hs₂ : s₂.BondGenerated bond₂)
    (toFun : {a : A₁ // a ∈ s₁.eligible} → {b : A₂ // b ∈ s₂.eligible})
    (invFun : {b : A₂ // b ∈ s₂.eligible} → {a : A₁ // a ∈ s₁.eligible})
    (left_inv : ∀ x, invFun (toFun x) = x)
    (right_inv : ∀ y, toFun (invFun y) = y)
    (bond_iff : ∀ x y, bond₁ x y ↔ bond₂ (toFun x) (toFun y)) :
    EligibleIso s₁ s₂ where
  toFun := toFun
  invFun := invFun
  left_inv := left_inv
  right_inv := right_inv
  preserves := by
    intro x y h
    exact (hs₂ _ _).2
      (BondClosure.map toFun (fun u v hb => (bond_iff u v).1 hb) ((hs₁ x y).1 h))
  reflects := by
    intro x y h
    have hinv : ∀ u v, bond₂ u v → bond₁ (invFun u) (invFun v) := by
      intro u v hb
      apply (bond_iff _ _).2
      rw [right_inv u, right_inv v]
      exact hb
    have hcl := BondClosure.map invFun hinv ((hs₂ _ _).1 h)
    rw [left_inv x, left_inv y] at hcl
    exact (hs₁ x y).2 hcl

end EligibleIso

/-- A presentation map that preserves and reflects admissibility and carries supports to images. -/
structure PresentationTransport {s₁ : Setting A₁ P₁} {s₂ : Setting A₂ P₂}
    (f : EligibleIso s₁ s₂) where
  /-- The map on presentations. -/
  toFun : P₁ → P₂
  /-- A presentation is admissible exactly when its image under `toFun` is admissible. -/
  admissible_iff : ∀ p, s₂.admissible (toFun p) ↔ s₁.admissible p
  /-- `toFun` carries a presentation's support to the corresponding support. -/
  support_eq : ∀ p, s₁.admissible p → s₂.support (toFun p) = f.image (s₁.support p)

namespace PresentationTransport

variable {s₁ : Setting A₁ P₁} {s₂ : Setting A₂ P₂} {f : EligibleIso s₁ s₂}

/-- Success is invariant under presentation transport. -/
theorem succeeds_iff (g : PresentationTransport f) (p : P₁) :
    s₁.Succeeds p ↔ s₂.Succeeds (g.toFun p) := by
  constructor
  · rintro ⟨hadm, hw⟩
    refine ⟨(g.admissible_iff p).2 hadm, ?_⟩
    rw [g.support_eq p hadm]
    exact (f.wholeConditions_image_iff (s₁.support_subset_eligible p hadm)).1 hw
  · rintro ⟨hadm₂, hw₂⟩
    have hadm : s₁.admissible p := (g.admissible_iff p).1 hadm₂
    refine ⟨hadm, ?_⟩
    rw [g.support_eq p hadm] at hw₂
    exact (f.wholeConditions_image_iff (s₁.support_subset_eligible p hadm)).2 hw₂

/-- Same-unit identity is invariant under presentation transport. -/
theorem sameUnit_iff (g : PresentationTransport f) (p q : P₁) :
    s₁.SameUnit p q ↔ s₂.SameUnit (g.toFun p) (g.toFun q) := by
  constructor
  · rintro ⟨hp, hq, heq⟩
    refine ⟨(g.succeeds_iff p).1 hp, (g.succeeds_iff q).1 hq, ?_⟩
    rw [g.support_eq p hp.1, g.support_eq q hq.1, heq]
  · rintro ⟨hp', hq', heq'⟩
    have hp : s₁.Succeeds p := (g.succeeds_iff p).2 hp'
    have hq : s₁.Succeeds q := (g.succeeds_iff q).2 hq'
    refine ⟨hp, hq, ?_⟩
    rw [g.support_eq p hp.1, g.support_eq q hq.1] at heq'
    exact (f.image_eq_iff (s₁.support_subset_eligible p hp.1)
      (s₁.support_subset_eligible q hq.1)).1 heq'

/-- Distinct-unit judgments are invariant under presentation transport. -/
theorem distinctUnits_iff (g : PresentationTransport f) (p q : P₁) :
    s₁.DistinctUnits p q ↔ s₂.DistinctUnits (g.toFun p) (g.toFun q) := by
  constructor
  · rintro ⟨hp, hq, hd⟩
    refine ⟨(g.succeeds_iff p).1 hp, (g.succeeds_iff q).1 hq, ?_⟩
    rw [g.support_eq p hp.1, g.support_eq q hq.1]
    exact (f.image_disjoint_iff (s₁.support_subset_eligible p hp.1)).2 hd
  · rintro ⟨hp', hq', hd'⟩
    have hp : s₁.Succeeds p := (g.succeeds_iff p).2 hp'
    have hq : s₁.Succeeds q := (g.succeeds_iff q).2 hq'
    refine ⟨hp, hq, ?_⟩
    rw [g.support_eq p hp.1, g.support_eq q hq.1] at hd'
    exact (f.image_disjoint_iff (s₁.support_subset_eligible p hp.1)).1 hd'

end PresentationTransport

end

end SE.Individuation.Structural
