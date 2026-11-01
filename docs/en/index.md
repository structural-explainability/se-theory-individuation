# SE Theory: Individuation

Lean 4 formalization of foundational
Individuation theory for Structural Explainability.

Individuation asks under what formal conditions a presentation
picks out exactly one whole,
given a stated criterion of whole co-membership.

This repository formalizes structural settings,
the conditions a presentation must meet to succeed,
same-unit and distinct-unit judgments,
one connectivity construction of whole co-membership,
transport of these results between settings, and
the connection to the Persistence commitment calculus.

- [Lean API Reference](https://structural-explainability.github.io/se-theory-individuation/lean/)
- [GitHub Repository](https://github.com/structural-explainability/se-theory-individuation)
- [Research Doubts and Open Questions](https://github.com/structural-explainability/se-theory-individuation/blob/main/DOUBTS.md)
- [Research Decisions](https://github.com/structural-explainability/se-theory-individuation/blob/main/DECISIONS.md)

## Individuation

A structural setting fixes a granularity.
It supplies eligible atoms,
a presentation-admissibility predicate,
a support function from presentations to sets of atoms, and
an equivalence relation on eligible atoms read as whole co-membership.
That relation is not strict identity of atoms.

A presentation succeeds when it is admissible and
its support is exactly one equivalence class of eligible atoms.
Same-unit and distinct-unit judgments are guarded by success:
two successful presentations identify
the same unit when their supports are equal, and
distinct units when their supports share no atom.

The connection between the repositories is equivalence
under declared criteria.

Individuation supplies or constructs a whole co-membership
equivalence on eligible atoms.
The Interpretive Kernel starts with a declared equivalence
on frames and derives the least equivalence on outputs
needed to preserve coherence under a stated interpretation.

These are different constructions, but both make the
consequences of declared identifications explicit.

Both use equivalence closure in particular constructions.
Individuation establishes finite-path characterizations
and generator-difference witnesses.
The kernel computes finite derivations and
probe-level disagreement witnesses.

The repositories do not import or call one another.
Connecting their constructions in an application requires
explicit choices of carriers, mappings, and interpretation.

Neither repository establishes that a proposed identity
criterion correctly identifies the intended referents.
Individuation formalizes consequences of the chosen
co-membership criterion.
The kernel computes consequences of a declared grouping
under an interpretation.

Their shared contribution is to **expose identity commitments**
**without treating formal coherence as scientific validation**.

## Dependencies

This repository is a theory-layer repository
for Structural Explainability.

It depends on Mathlib and on two Structural Explainability
theory repositories:

- Neutral Substrate, for the individuation account that the construction instantiates
- Persistence, for the commitment calculus

It does not import Transformation's operator taxonomy,
effect dimensions, or state models.

The connection to Persistence is stated for carriers in `Type`,
so those modules specialize atoms and presentations to universe 0.

## Related Repositories

### Interpretive Kernel

[se-interpretive-kernel](https://github.com/structural-explainability/se-interpretive-kernel)
is a separate Python package.
It asks a different question from this repository.

This repository asks how a criterion of co-membership picks out wholes.
The kernel starts from a grouping of items that someone has declared.
It asks whether that grouping is consistent
with what an interpretation says about those items.
When it is not, it reports a finite witness and
the identifications the grouping would force on the outputs.
It can also list where two groupings disagree.

The two meet at one point: a grouping.
The wholes constructed here divide the eligible atoms into groups.
A set of wholes can be read as the kind of grouping the kernel accepts.

This repository does not import or call the kernel.
The kernel does not import or call this repository.
Neither one decides which grouping is correct.
Each reports what a stated choice commits you to,
not whether the choice is right.

Both build a grouping by closing a set of stated pairs under equivalence.
Both explain a result with a finite chain and a witness.
They share a method and no code.

## Scope

Repository scope is defined in `SE_MANIFEST.toml`.

## Exclusions

Repository exclusions are defined in `SE_MANIFEST.toml`.

## Import

Downstream Lean projects should import the public surface:

`import SE.Individuation`
