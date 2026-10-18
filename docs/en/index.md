# SE Theory: Individuation

Lean 4 formalization of foundational
Individuation theory for Structural Explainability.

Individuation asks .

This repository formalizes individuation .

- [Lean API Reference](https://structural-explainability.github.io/se-theory-individuation/lean/)
- [GitHub Repository](https://github.com/structural-explainability/se-theory-individuation)

## Individuation

Individuation .

## Dependencies

This repository is a foundational theory-layer repository
for Structural Explainability.

It depends on Mathlib but has no dependency on another
Structural Explainability theory repository.

## Covers

This repository covers:

- individuation
- Lean-side reference vocabulary
- machine-readable public-surface registries
- public Lean import surface

## Owns

This repository owns:

- the public import surface `SE/Individuation.lean`
- the repository-level aggregator `SE.lean`
- reference artifacts under `reference/`
- generated individuation artifacts under `data/individuation/`

## Out of Scope

This repository does not own:

- neutral substrate primitives
- transformation operator, family, or kind definitions
- transformation taxonomy lifts
- transformation effect dimensions or state models
- dimension-specific observational bridges
- identity regime definitions or profiles
- domain-specific identity criteria or their scientific justification
- validation and export tooling for artifacts
- domain mappings
- runtime systems
- operational policy

## Design Constraints

Lean source files are authoritative for formal theory semantics and proofs.

Reference registries describe the registered public surface
and must correspond to that Lean surface.

Python and generated data may mirror, validate, export,
or document the Lean surface.
They must not define theory semantics independently of Lean.

See the Lean source files and reference registries for current values.

## Documentation Constraints

Documentation is descriptive only.
It may provide orientation, summaries, and navigation.

It must not introduce formal semantics absent from Lean.

Machine-readable artifacts mirror the Lean surface
and reference registries under `data/individuation/`.

## Import

Downstream Lean projects should import the public surface:

`import SE.Individuation`

## Tooling

Python and other tooling may be used for:

- documentation generation
- formatting and linting
- repository automation
- reference artifact validation
- generated contract export checks

They must not:

- define correctness
- validate theory semantics independently of Lean
- replace Lean definitions or proofs
- introduce downstream theory dependencies
