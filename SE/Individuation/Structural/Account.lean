/-
Copyright (c) 2026 Denise M. Case. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denise M. Case
-/
module

public import SE.Individuation.Structural.SameUnit
public import SE.Substrate.ReferentialRegime.Individuation

set_option autoImplicit false

/-!
# Neutral Substrate Adapter

SE.Individuation.Structural.Account

Constructs `SE.Substrate.IndividuationAccount (Set A)` from the structural construction:

- `Context`: the structural setting;
- `Presentation`: the fixed presentation type;
- `admissiblePresentation`: the setting's admissibility predicate;
- `one`: success (admissibility and the whole conditions);
- `sameUnit`: successful presentations with equal support;
- `presents`: success, with the complete support equal to the set-valued referent.

Set-valued referents are a local extensional realization. They do not identify carrier
equality with identity throughout the framework. Assigning this account to one of the three
referent kinds belongs to construction of a particular `IndividuationRegime` (IR-CARRIER).
-/

namespace SE.Individuation.Structural

universe u

@[expose] public section

/-- The structural individuation account over set-valued referents. -/
def individuationAccount (A : Type u) (Presentation : Type u) :
    SE.Substrate.IndividuationAccount.{u} (MathlibMini.Set A) where
  Context := Setting A Presentation
  Presentation := Presentation
  presents := fun c p W => c.Succeeds p ∧ c.support p = W
  admissiblePresentation := fun c p => c.admissible p
  one := fun c p => c.Succeeds p
  sameUnit := fun c p q => c.SameUnit p q

namespace individuationAccount

variable {A Presentation : Type u} {c : Setting A Presentation}
  {p q : Presentation} {W W' : MathlibMini.Set A}

/-! ### Adapter equations -/

/-- A presentation is admissible exactly when the account's admissibility condition holds. -/
theorem admissiblePresentation_iff :
    (individuationAccount A Presentation).admissiblePresentation c p ↔ c.admissible p :=
  Iff.rfl

/-- An element counts as one exactly when the account's unity condition holds. -/
theorem one_iff :
    (individuationAccount A Presentation).one c p ↔ c.Succeeds p :=
  Iff.rfl

/-- Two elements are in the same unit exactly when the account's same-unit condition holds. -/
theorem sameUnit_iff :
    (individuationAccount A Presentation).sameUnit c p q ↔ c.SameUnit p q :=
  Iff.rfl

/-- A presentation presents a whole exactly when the account's presentation condition holds. -/
theorem presents_iff :
    (individuationAccount A Presentation).presents c p W ↔
      c.Succeeds p ∧ c.support p = W :=
  Iff.rfl

/-! ### Success guards -/

/-- Whatever counts as one is admissible. -/
theorem one_admissible
    (h : (individuationAccount A Presentation).one c p) :
    (individuationAccount A Presentation).admissiblePresentation c p :=
  h.1

/-- Whatever a presentation presents counts as one. -/
theorem presents_one
    (h : (individuationAccount A Presentation).presents c p W) :
    (individuationAccount A Presentation).one c p :=
  h.1

/-- If two elements are in the same unit, the left one counts as one. -/
theorem sameUnit_one_left
    (h : (individuationAccount A Presentation).sameUnit c p q) :
    (individuationAccount A Presentation).one c p :=
  h.1

/-- If two elements are in the same unit, the right one counts as one. -/
theorem sameUnit_one_right
    (h : (individuationAccount A Presentation).sameUnit c p q) :
    (individuationAccount A Presentation).one c q :=
  h.2.1

/-- A successful presentation presents exactly its support, and nothing else. -/
theorem one_iff_presents_support :
    (individuationAccount A Presentation).one c p ↔
      (individuationAccount A Presentation).presents c p (c.support p) :=
  ⟨fun h => ⟨h, rfl⟩, fun h => h.1⟩

/-- A presentation presents at most one whole. -/
theorem presents_unique
    (h : (individuationAccount A Presentation).presents c p W)
    (h' : (individuationAccount A Presentation).presents c p W') : W = W' :=
  h.2.symm.trans h'.2

/-- Same unit is exactly: both presentations present a common set-valued referent. -/
theorem sameUnit_iff_common_presents :
    (individuationAccount A Presentation).sameUnit c p q ↔
      ∃ W, (individuationAccount A Presentation).presents c p W ∧
        (individuationAccount A Presentation).presents c q W := by
  constructor
  · rintro ⟨hp, hq, heq⟩
    exact ⟨c.support p, ⟨hp, rfl⟩, ⟨hq, heq.symm⟩⟩
  · rintro ⟨W, ⟨hp, hpW⟩, ⟨hq, hqW⟩⟩
    exact ⟨hp, hq, hpW.trans hqW.symm⟩

/-- The adapter's same-unit relation at a presentation with itself is exactly its success. -/
theorem sameUnit_self_iff :
    (individuationAccount A Presentation).sameUnit c p p ↔
      (individuationAccount A Presentation).one c p :=
  Setting.sameUnit_refl_iff c p

end individuationAccount

end

end SE.Individuation.Structural
