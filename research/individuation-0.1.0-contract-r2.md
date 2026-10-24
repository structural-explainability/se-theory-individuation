# Individuation 0.1.0: Candidate Semantic Contract (revision 2)

Status: conditional structural construction implemented in Lean;
scientific adequacy OPEN; CHEM-01 grounding incomplete.

## Objectives

Develop a conditional mathematical account of exclusive structural wholes,
connect it explicitly to Neutral Substrate and Persistence, and
test whether the account agrees with independently warranted judgments
for an independently justified kind of whole.

We are currently looking for evidence
showing whether a justified structural criterion
correctly individuates something we can independently recognize
as one whole and (equally importantly) where it fails.

## Primary Question

For a stated kind of whole, do the exclusive-whole conditions, with the
co-membership relation supplied for that kind, agree with independently
warranted whole, same-unit, and distinct-unit judgments?

The conditional construction below is supporting work.
It establishes what follows from the criterion.
It does not answer this question.

Separated Questions:

1. **Construction:** what follows mathematically from the stated structural criterion?
2. **Adequacy:** for the intended kind, does the criterion agree with
   independently warranted judgments, and where does it not?

Conditional formalization is governed by the Stage section.
It does not resolve the adequacy question.

The component construction is one candidate account.
It does not determine the architecture of all future Individuation theories.

## Established Background

- Neutral Substrate owns `SE.Substrate.IndividuationAccount`.
- Its fields are `Context`, `Presentation`, `presents`, `admissiblePresentation`, `one`, and `sameUnit`.
- The interface has no distinctness field and imposes no general equivalence laws.
- It does not identify same-unit identity with presentation equality or referent-carrier equality.
- An individual account accepts an arbitrary referent carrier.
- Constructing an `IndividuationRegime` additionally requires accounts for the entity, occurrence, and institutional-artifact carriers.
- Persistence supplies generic commitment machinery over a carrier stated as `Type`.
- That machinery does not independently justify its supplied relations, constraints, or continuation licences.

Inspected-source provenance:

- https://github.com/structural-explainability/se-theory-neutral-substrate/blob/v0.11.0/SE/Substrate/ReferentialRegime/Individuation.lean
- https://github.com/structural-explainability/se-theory-persistence/blob/v0.5.0/SE/Persistence/Commitment/Consistency.lean
- https://github.com/structural-explainability/se-theory-persistence/blob/v0.5.0/SE/Persistence/Commitment/Status.lean
- https://github.com/structural-explainability/se-theory-persistence/blob/v0.5.0/SE/Persistence/Commitment/Observed.lean

Not inspected: `SE.Persistence.Relation.Generated` and the generator-comparison
results referenced under Explanation and Witnesses.
Statements relying on them are provisional until that source is inspected
and added to the provenance (IND-PROVENANCE).

## Semantic Gap

Neutral Substrate leaves `one` and `sameUnit` abstract by design:
no equivalence laws, no distinctness field, no decidability.
This is deliberate abstraction, not omission.

This candidate adds structure the interface does not supply:

- `sameUnit` is an equivalence relation on successful presentations;
- `one` entails nonemptiness, internal co-membership, and saturation;
- a distinctness predicate is exposed by the Individuation API.

These are proposals of this candidate.
No semantics is inferred from the interface's silence.

## Source Compatibility

- **Preserved:** `sameUnit` is not identified with presentation equality or
  carrier equality; all `IndividuationAccount` fields are unchanged.
- **Strengthened (this candidate only):** the three additions above.
- **Revised:** none proposed in Neutral Substrate or Persistence.
- **Intentionally weaker than this candidate:** the `IndividuationAccount`
  interface (no laws) and Persistence's commitment calculus
  (equivalence laws only, no class-count limits).

## Terminology Boundary

- **Candidate presentation:** an object evaluated by an individuation account.
- **Support:** the atoms represented by a presentation at a setting.
- **Whole co-membership:** the relation that two atoms belong to the same whole under the specified criterion.
- **Co-membership generator:** the relation from which co-membership is generated
  (the bond relation in the connectivity instance).
  In a grounding case it is named for the kind and is not assumed to coincide
  with that kind's own use of the word "bond".
- **Same-unit identity:** the relation between successful presentations of one whole.
- **Observation map:** Persistence's map from carrier elements to observation values.
- **Reference:** an object evaluated by a co-reference account.
- **Presentation admissibility:** eligibility for individuation evaluation.
- **Relation admissibility:** Persistence's condition that an equivalence relation respects supplied same and distinct commitments.
- **Framework admissibility:** Neutral Substrate's condition on interpretive frameworks.
- **Commitment consistency:** compatibility of supplied relational commitments.
- **Logical consistency:** non-entailment of contradiction under a consequence system.

Use qualified names where these meanings could be confused.

Support is a presentation-to-atoms interpretation.
It is not reference-to-referent denotation and does not supply co-reference lifting.

The adapter's `presents` relation supplies a local presentation-to-referent interpretation.
Its existence does not resolve the separate semantics of references.

## Candidate Scope

The construction concerns **exclusive wholes at a fixed setting and granularity**.

Successful whole supports are equivalence classes and therefore are equal or disjoint.
Distinct wholes sharing constituents at that setting and granularity fall outside this account.

This partition restriction is substantive.
It must not become a general requirement of Individuation.

Connectivity is one construction of the equivalence relation.
Several results require only equivalence-class structure and should be stated at that generality.

Two commitments are built into the criterion and are separate:

- **Exclusivity:** successful supports are equal or disjoint.
- **Extensionality:** successful presentations with equal supports identify
  the same unit at that setting and granularity.

Coextensive distinct wholes violate extensionality without violating exclusivity.
Both are substantive restrictions of this candidate, not requirements of Individuation.

## Structural Construction

Fix:

- an atom carrier `A : Type u`;
- a presentation type `Presentation : Type u`.

At each setting `c`, supply:

- an eligible domain `B_c ⊆ A`;
- a presentation-admissibility predicate `adm_c`;
- a support function `supp_c : Presentation → Set A`;
- containment of admissible supports in `B_c`;
- an equivalence relation `E_c` on the subtype of eligible atoms.

Interpret `E_c` as whole co-membership under the proposed criterion.

It does not mean equality or strict identity of the atoms.

### Connectivity Instance

Supply a structural bond relation `b_c` on eligible atoms.
Its direction is immaterial: the generated equivalence closes it symmetrically.

Construct `E_c` as the equivalence relation generated by those bonds,
equivalently finite-path connectivity within the eligible domain.

Using this construction scientifically requires
justifying why bond-connected atoms belong to the same intended whole.

### Successful Whole Presentation

An admissible presentation with support `W` succeeds exactly when:

1. **Nonemptiness:** `W` contains an eligible atom.
2. **Internal co-membership:** every two atoms in `W` are `E_c`-related.
3. **Saturation:** every eligible atom `E_c`-related to an atom in `W` belongs to `W`.

Prove that these conditions characterize exactly one `E_c`-class.

For the connectivity instance,
this is one maximal connected component within the selected boundary.

### Same Unit

Two presentations identify the same unit exactly when
both succeed and their supports are equal.

### Distinct Units

Two presentations identify distinct units exactly when
both succeed and their supports are disjoint.

Expose this distinctness predicate through the Individuation public API.
It is not a field of Neutral Substrate's `IndividuationAccount`.

Prove that distinctness is equivalent to failure of same-unit identity
on successful presentations under this exclusive-whole account.

This mathematical complement does not justify treating failure to
establish sameness from evidence as established distinctness.

## Proposed Mathematical Results

The following remain proof obligations until formalized and checked.

### Whole Characterization

An admissible presentation succeeds exactly when its support
is one eligible equivalence class.

Nonemptiness supplies a representative.
Internal co-membership and saturation establish the two set inclusions.

### Overlap Characterization

Two successful presentations identify the same unit exactly when their supports overlap.

The success hypotheses are essential.

### Same-or-Distinct Dichotomy

Two successful supports are equal or disjoint, and cannot be both.

The exclusion of both uses nonemptiness of successful supports.

This is a result of the exclusive-whole construction.
It does not establish that all intended wholes satisfy exclusivity.

### Equivalence on Successful Presentations

Same-unit identity is an equivalence relation on the subtype of successful presentations.

Its success-guarded extension to all candidate presentations is not globally reflexive.

### Lossless Re-presentation

At a fixed setting, admissible presentations with equal supports have the same success status.

When successful, they identify the same unit despite differences in format, labels, or annotation.

### Structural Transport

A bijection between eligible domains that preserves and reflects `E_c`
transports whole supports and their equality/disjointness relations.

For the connectivity instance, preservation and reflection of bonds
are sufficient to establish the required connectivity correspondence.

Presentation-level transport additionally requires a presentation map that:

- preserves and reflects admissibility;
- carries supports to their corresponding images.

These results establish invariance of the construction under the stated transport.
They do not establish strict identity across settings.

### Representation Availability

The structural results do not guarantee that every whole has a presentation.

Any claim that every eligible class is representable requires
a separate presentation-coverage condition and proof.

## Scientific Grounding

An application must independently justify:

- the intended kind of whole;
- the selected setting and granularity;
- the atom interpretation;
- the eligible boundary;
- the proposed co-membership relation or bonds;
- the interpretation and accuracy of support.

Calling a bond "constitutive" does not discharge these obligations.

A boundary or bond chosen solely to reproduce the desired component partition
would make the grounding circular.

Justification may arise from a constitutive specification,
an independently justified mathematical construction, or appropriate empirical evidence.

### Required Grounding Case

1. Specify the intended kind of whole independently of the component construction.
2. Justify its atoms, boundary, and structural relations.
3. Obtain independently warranted whole, same-unit, and distinct-unit judgments.
4. Compare those judgments with the construction's consequences.
5. Include a plausible case capable of forcing rejection or narrowing.
6. Record the supported scope and remaining limitations.

No completed grounding case is established by this contract.

### Scientific Obligations

#### Soundness and completeness

Let `J_whole`, `J_same`, `J_distinct` be independently warranted judgments for
the intended kind at a fixed setting.

- Sound: success implies `J_whole`; same-unit implies `J_same`; distinct-unit implies `J_distinct`.
- Complete: the converses, over judged cases only.

Judgments are partial. No claim is made about unjudged cases.

#### Support faithfulness

The interpretation must justify that support preserves every distinction the
intended identity judgment draws:
presentations of warranted-distinct wholes have different supports, and
presentations of the warranted-same whole have equal supports.
A relevant distinction not recoverable from support lies outside this account.

#### Singleton wholes

An eligible atom with no bond forms a singleton class and satisfies the whole
conditions. Whether a singleton is a whole of the intended kind is decided by
independently warranted judgments for that kind, not by the construction.

#### Refutation conditions

A counterexample to the candidate, as opposed to a bond set, is an independently
warranted judgment contradicting one of:

1. exclusivity (narrowing);
2. transitivity of co-membership;
3. sufficiency of the bond relation (warranted-separate wholes joined by independently justified bonds);
4. necessity of the bond relation (a warranted whole no independently justified bond connects).

The bond relation must be fixed independently of the judgment.
A disagreement localizes a defect among bond set, boundary, and judgment
only after further investigation.

#### Co-membership is not identity

Whole co-membership between atoms is never strict identity between atoms.
Only Persistence's generic relation calculus is used on atoms.
Its identity-specific readings are not imported.

### Grounding Case CHEM-01: Stable Molecular Species (adequacy test)

**Kind:** stable molecular species under stated conditions.

**Setting (all frozen before comparison):**
conditions (temperature, phase, isolated or condensed);
level of theory and basis;
geometry source and treatment (equilibrium or vibrationally averaged).
[TODO: record each.]

**Atoms and boundary:** atoms of the specified system;
the boundary is the system, recorded before comparison.

**Route 1, QTAIM neighbor relation:** two atoms are related when the electron
density at the fixed level of theory has a bond path between their nuclei.
Co-membership is the generated equivalence; wholes are connected components.

Notes on Route 1:

- The IUPAC Gold Book defines a chemical bond by reference to a stable
  independent molecular entity. Using that definition as Route 1 would make
  the comparison circular, so it is not used.
- A bond path is defined from the topology of the electron density, which does
  not use the species concept. Whether a bond path is a chemical bond is
  disputed in the literature, including by QTAIM proponents, and bond-path
  presence depends on nuclear geometry and vibration
  (for example Foroutannejad, Shahbazian and Marek, Chem. Eur. J. 20 (2014) 10140-10152).
- The relation is therefore named a neighbor relation, and
  "neighbor-connected atoms belong to one species" is the claim under test.

[TODO: confirm from primary QTAIM sources that the relation is independent of
the species concept and has no free parameter beyond the Setting.]

**Route 2, judgments:** species partition of each test system from experimental
or thermodynamic warrant.
[TODO: record source per system.]

**Pre-registration order:**

1. Record Route 2 judgments with sources, each classified contested or uncontested.
2. Record Route 1 parameters (the Setting above).
3. Record the decision rule below.
4. Only then compute Route 1 partitions.

Items 1 to 3 are not revised after item 4.

**Test systems** [TODO: select specific systems; warrant each judgment before recording]:

Uncontested. Agreement is recorded but carries little evidential weight,
because bond paths are commonly used as a tool to confirm bonds and so were
validated against chemical practice:

- a single monatomic atom (singleton pressure case);
- one small covalent molecule;
- two molecules at large separation (disconnected isomorphic copies).

Contested. These can force narrowing or rejection where independent warrant
for the judgment exists:

- a weakly bound dimer;
- an encapsulated noble-gas atom in a cage molecule;
- a growing ionic crystal fragment (boundary dependence; pressure cases 1 and 2).

**Decision rule (fixed before computation):**

1. A warranted judgment of two species sharing atoms (exclusivity failure):
   ACCEPT WITH NARROWING; the scope excludes such systems.
2. Neighbor-connected atoms warranted as belonging to different species
   (sufficiency or transitivity failure): REJECT the connectivity instance for
   this kind with this neighbor relation, unless the failure is confined to a
   named class of systems, in which case ACCEPT WITH NARROWING to exclude that class.
3. A warranted single species whose atoms are not neighbor-connected
   (necessity failure): same treatment as item 2.
4. A contested system with no recorded independent warrant for its judgment
   yields no verdict. It is recorded as unresolved, not as agreement or disagreement.
5. Agreement on all uncontested systems and on every verdict-yielding contested
   system means the criterion survives this test for the stated scope.
   This is not acceptance.

**Recorded limits:** scope is the selected systems at the recorded Setting.

### Grounding Case REPO-01: Repositories and Forks (scope-narrowing exhibit)

This case is not an adequacy test. Its warrant is institutional, not independent of the kind.

**Atoms, two readings:**

- commits: a repository and its fork share constituents, so the pair falls outside exclusivity (narrowing case);
- tree snapshots: a fork is an isomorphic copy, distinct unless ancestry is a bond (pressure case 6).

**Judgments:** taken from the platform's documented model.
[TODO: record source.]

**Question tested:** whether a structural criterion reconstructs the institutional
rule without being given it.

**Recorded limits:** scope is the stated reading of atoms and the stated rule.

## Neutral Substrate Adapter

Construct:

`SE.Substrate.IndividuationAccount (Set A)`

with:

- `Context`: the structural setting and its mathematical conditions;
- `Presentation`: the fixed presentation type;
- `admissiblePresentation`: `adm_c`;
- `one`: admissibility and the whole conditions;
- `sameUnit`: successful presentations with equal support;
- `presents`: success and equality between complete support and the supplied set-valued referent representation.

Prove the adapter equations and success guards.

Set-valued referents are a local extensional realization.
They do not identify carrier equality with identity throughout the framework.

An individual adapter does not require assignment to one of the three referent kinds.
Such assignment belongs to construction of a particular `IndividuationRegime`
(IR-CARRIER).

## Persistence Connection: Successful Presentations

At each setting, use successful presentations as the carrier.

Let:

- `P` be same-unit judgments;
- `D` be distinct-unit judgments;
- `E` be support equality.

Prove:

- `E` is Persistence-admissible for `P` and `D`;
- the commitments are consistent;
- `E` is the unique admissible relation;
- no pair is undetermined under these exact commitments;
- `D` coincides with the pairs separated by the support observation map.

Hypotheses used: nonemptiness of successful supports (for `D ∩ E = ∅` and for
disjoint implies unequal) and the same-or-distinct dichotomy
(for uniqueness and for unequal implies disjoint).

The coincidence of `D` with the pairs separated by the support observation map
depends on exclusivity through the dichotomy.
It does not carry over to criteria that admit overlapping wholes (IND-GENERAL).

This is a soundness construction and establishes mathematical correctness only.
Because one criterion determines both `P` and `D`,
consistency does not independently validate the criterion against practice.

## Persistence Connection: Whole Co-membership Constraints

A second use of the generic commitment calculus operates on eligible atoms.

For the connectivity instance, supply:

- `P`: the co-membership generator interpreted as same-whole co-membership commitments;
- `D`: independently warranted commitments that two atoms belong to different wholes.

`D` must not mean merely that the atoms are unequal or distinct individuals.
Different atoms can belong to the same whole.

Here, the generated equivalence is interpreted as whole co-membership, not strict atom identity.
This is an application of the generic relation calculus,
not a claim that Persistence identifies constituents with one another.

### Boundary Compatibility

Check whether any pair in `D` lies in the equivalence generated by `P`.

Consistency establishes compatibility with the supplied separation commitments.
It does not establish that the resulting partition is uniquely correct.

A rejecting result identifies disagreement among the proposed bonds and
independently warranted boundaries.
Determining which input is defective requires further investigation.

### Explanation and Witnesses

Use the finite-path characterization of generated equivalence to explain
how bonds connect a pair required to remain in different wholes.

Under consistent initial commitments, a forbidden proposed bond
is one whose addition would connect a prohibited pair.

When two bond sets generate different co-membership relations,
generator-comparison results can expose a bond on one side whose endpoints are not connected on the other.
(Provisional: the source of these results is not yet inspected; see IND-PROVENANCE.)

Such a witness localizes a difference.
It does not independently identify a scientifically erroneous bond.

### Changing Boundaries

Comparisons across eligible domains require an explicit common carrier or transport.

A boundary change can introduce or remove connecting paths.
Inclusion or injection of atoms alone does not establish preservation or reflection of connectivity.

State the required correspondence before applying commitment-comparison results.

## Conditional Merge and Fork Constraints

Merge and fork consequences follow from Persistence's generic commitment
calculus under a continuation interpretation.
That interpretation, with its stage carrier and licences, belongs to Identity
Regimes (IR-CONTINUATION). It is outside this contract.
No merge or fork claim is made here.

## Adversarial Cases

### Construction Checks

1. Empty support fails nonemptiness.
2. A disconnected aggregate fails the connectivity criterion.
3. A proper connected part fails saturation.
4. Different successful presentations of one support identify one unit.
5. Disconnected isomorphic copies remain distinct.
6. Overlap of arbitrary subsets does not establish successful-whole identity.
7. A whole may exist without any available presentation unless coverage is supplied.

### Grounding Pressure Cases

1. A bridge can create one component where independently warranted judgments require separate wholes.
2. A manipulated boundary can produce the desired partition without justification.
3. Incomplete support can conceal a failed saturation condition.
4. Association or evidential-match links can connect things without constituting one whole.
5. Distinct wholes sharing constituents violate the exclusive-whole scope.
6. Ancestry links between a repository and its forks can connect them without establishing one whole. This is a proposed pressure case requiring an explicit model and independent judgments.
7. An isolated eligible atom satisfies the whole conditions.
8. Two warranted-distinct wholes with equal supports (extensionality failure).
9. A distinction relevant to the intended judgment that support does not record.

### Integration Checks

1. Atom inequality must not be used as different-whole commitment.
2. Different contexts must not be silently identified.
3. A structural isomorphism must not be treated as strict continuation.
4. A merge must not license two asserted-distinct predecessors as the same successor.
5. A fork must not license one predecessor as two asserted-distinct successors.
6. Rejecting simultaneous continuations must not be reported as selecting one.
7. Observation differences must not become strict distinctions without justification.

Checks 3 to 6 concern regime-level continuation.
They are recorded here as guards; their resolution belongs to IR-CONTINUATION.

A scientific counterexample must lead to rejection, revision, or justified narrowing.

## Context and Evidence Ownership

### Three-way Alignment

Individuation, Co-reference, and Persistence expose separate context or setting types.

Identity Regimes owns their composition for particular regimes, including:

- alignment of applicable contexts and settings;
- reference-to-referent and presentation connections;
- connections between successful presentations and eligible stages;
- construction of substantive `PersistenceAccount` instances;
- compatibility conditions among the accounts.

Each foundational theory supplies the interfaces and results needed for that composition.

Neutral Substrate retains its dependency independence.

### Evidence Responsibilities

Individuation owns warrant for:

- singular unity;
- presentation support;
- presentation-level same-unit and distinct-unit judgments.

Co-reference owns:

- reference denotation;
- reference resolution;
- co-reference judgments and their evidential warrant.

A record can participate in either task. Ownership follows the judgment being established, not the storage format.

## Universe Policy

Keep the structural construction universe-polymorphic where supported.

The initial adapters to Persistence's current commitment calculus may specialize their carriers to universe 0.

That specialization does not require restricting the entire Individuation theory.

Generalizing Persistence remains a separate upstream change.

## Proposed Module Organization

Dependency declarations and resolved revisions belong in `lakefile.toml` and `lake-manifest.json`.

- `SE/Individuation.lean`: public import surface.
- `SE/Individuation/Structural/Setting.lean`: settings, eligible atoms, support, and equivalence structure.
- `SE/Individuation/Structural/Connectivity.lean`: bond-generated co-membership instance.
- `SE/Individuation/Structural/Whole.lean`: whole conditions and characterization.
- `SE/Individuation/Structural/SameUnit.lean`: same/distinct judgments.
- `SE/Individuation/Structural/Transport.lean`: support and presentation transport.
- `SE/Individuation/Structural/Account.lean`: Neutral Substrate adapter.
- `SE/Individuation/Structural/Commitments.lean`: successful-presentation soundness connection.
- `SE/Individuation/Structural/BoundaryCompatibility.lean`: bond/separation compatibility and witnesses.
- `SETest/Individuation/Structural.lean`: finite witnesses and essential-hypothesis counterexamples.

Cross-setting regime constructions remain outside this proposed module list.

Reference declarations must describe implemented public declarations and their actual proof status.

## Open Ledger

- **IND-GROUNDING:** independently justified application.
  Owner: Individuation. Not deferred. Blocks acceptance: yes.
  Verification: CHEM-01 completed as pre-registered; independent adversarial
  review given the CHEM-01 pre-registration without the author's reasoning path;
  human inspection.
- **IND-SUPPORT:** support faithfulness per kind.
  Owner: Individuation. Not deferred. Blocks acceptance: yes.
  Verification: per-kind statement of preserved distinctions, tested in CHEM-01.
- **IND-PROVENANCE:** inspect `SE.Persistence.Relation.Generated` and the
  generator-comparison results used under Explanation and Witnesses.
  Owner: Individuation. Not deferred. Blocks acceptance: yes for the witness
  claims; no for the rest of the construction.
  Verification: source inspected and added to the provenance list, or the
  claims removed.
- **IND-GENERAL:** other unity criteria, including overlapping wholes.
  Owner: Individuation. Deferred: exclusivity is a recorded narrowing and
  overlapping wholes need a separate criterion. Blocks: no.
  Verification: a criterion admitting overlap with its own grounding case.
- **IND-EVIDENCE:** evidence for unity, support, presentation-level identity.
  Owner: Individuation. Deferred: CHEM-01 takes warranted judgments as inputs. Blocks: no.
  Verification: a stated warrant standard for those judgments.
- **REF-DENOTATION:** reference denotation, resolution, co-reference lifting.
  Owner: Co-reference. Deferred: this contract works at presentation level. Blocks: no.
  Verification: Co-reference results with explicit denotation semantics.
- **IR-ALIGNMENT:** compose the three account contexts and semantic connections.
  Owner: Identity Regimes. Deferred: needs all three foundational theories. Blocks: no.
  Verification: composition with stated compatibility conditions.
- **IR-CARRIER:** `IndividuationRegime` takes accounts over `R.Entity`,
  `R.Occurrence`, `R.InstitutionalArtifact`; a `Set A`-valued account enters a
  regime only if that carrier is supplied or a map from `Set A` is constructed.
  Owner: Identity Regimes. Deferred: regime-level choice. Blocks: no.
  Verification: explicit carrier assignment or map.
- **IR-CONTINUATION:** stage constructions, continuation licences, merge/fork.
  Owner: Identity Regimes. Deferred: needs the stage carrier. Blocks: no.
  Verification: regime construction with justified licences.
- **IND-NEUTRALITY:** compatibility of a concrete interpretation with admissible
  causal and normative frameworks.
  Owner: Individuation for its criteria; Identity Regimes for composed applications.
  Deferred: depends on a concrete interpretation (CHEM-01).
  Blocks acceptance: yes for any substantive application; no for the
  conditional construction.
  Verification: neutrality check against the framework-admissibility condition.
- **IND-UNIVERSE:** generalize Persistence's carrier universes.
  Owner: Persistence. Deferred: current adapters specialize to universe 0. Blocks: no.
  Verification: a Persistence release generalizing carriers.
- **IND-LOGIC:** link commitment consistency to logical consistency.
  Owner: Individuation. Deferred: not required by the construction. Blocks: no.
  Verification: a justified connection with stated scope.

Ownership does not constitute discharge.

## Stage

- Mathematical construction: implemented in Lean.
- Theory-construction status: scientific adequacy remains unresolved.
- Theory-acceptance status: OPEN.
- CHEM-01: grounding and independent adequacy assessment incomplete.
- Formal correctness does not establish that the supplied whole
  co-membership or support semantics are adequate for intended referents.

## Development and Acceptance Status

Complete the CHEM-01 grounding case using independently warranted
judgments and the documented comparison procedure.

Scientific adequacy remains **OPEN**.

The broader question of independently justified individuation remains unresolved
until a grounding case supports the proposed criterion or forces its revision.

The documented review history does not yet establish satisfaction of the independent-review gate.
Reviews that contributed to drafting do not count as independent.
No Lean compilation is claimed.

Before accepting a substantive application:

- complete the grounding case;
- obtain independent adversarial review;
- inspect the final candidate and accepted limits;
- verify the formal construction and adapters;
- distinguish mathematical correctness, scientific adequacy, and theoretical contribution.

Any 0.1.0 release must describe its actual achievements and remaining obligations.
Conditional construction results must not be presented as a complete theory of individuation.

## Protocols

- https://github.com/structural-explainability/se-protocols-research/blob/main/protocols/theory-construction/SKILL.md
- https://github.com/structural-explainability/se-protocols-research/blob/main/protocols/theory-acceptance/SKILL.md
