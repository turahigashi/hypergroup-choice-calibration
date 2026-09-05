# Choice in the Fundamental Theorem of Hypergroups

A machine-checked axiom-dependency calibration, in Lean 4, of where the axiom of choice enters the
fundamental theorem of hypergroup theory.

This repository is the artifact accompanying the paper *Choice in the Fundamental Theorem of
Hypergroups: A Machine-Checked Axiom-Dependency Calibration*.

The version cited in the paper is the annotated tag [`v1.0.4-pre`](https://github.com/turahigashi/hypergroup-choice-calibration/tree/v1.0.4-pre),
archived at [doi:10.5281/zenodo.22336441](https://doi.org/10.5281/zenodo.22336441). That snapshot,
not the current state of `main`, is the object the paper's measurements were taken from.

## The result, in one table

A **hypergroup** (Marty, 1934) has an associative, reproductive operation whose values are non-empty
*sets*. A **strongly regular** equivalence `R` induces the usual group quotient. The standard
construction used in the classical treatments examined for the paper selects a representative from
`a ∘ b`; strong regularity makes its class independent of that selection. The following footprints
are produced by `#print axioms` when this development is built.

| step | axioms |
|---|---|
| strongly regular ⟹ group laws **modulo `R`** | **none** |
| the bridge, given a local `R`-description operator | **none** |
| `RDescription → selections → GroupModuloData` (both halves) | **none** |
| a description operator, realized classically | `Classical.choice` |
| selected data ⟹ `Group` on the quotient type | `propext`, `Quot.sound` |
| a *witnessed* hypergroup ⟹ `Group` on the quotient type | `propext`, `Quot.sound` |
| the standard route (`srQuotientGroup`) | `propext`, `Classical.choice`, `Quot.sound` |
| `β` is transitive, i.e. `β = β*` (Freni, via Gutan) | `propext`, `Quot.sound` |

So the classical choice used by the standard construction is confined, in the factorization studied
here, to one layer — the passage from propositional existence to *selected* algebraic data (a product
representative, a unit, and inverses). That layer factors through a local selector interface having
the same total-functional-relation-to-map shape as the setoid *axiom of descriptions* (unique
choice). We do not claim that this interface is minimal, necessary, or equivalent to any particular
global choice principle.

**These are one-sided dependency upper bounds**, measured on particular proof terms. They are not
reverse-mathematical lower bounds: nothing here shows that any choice principle is *necessary*.

## Layout

| | |
|---|---|
| `HypergroupCalibration.lean` | the whole development, self-contained: only Mathlib is required |
| `logs/axioms.txt` | the recorded `#print axioms` output |
| `scripts/verify.sh` | rebuilds and checks that the audit is reproduced **exactly** |

Two namespaces:

* `Hypergroups` — hyperoperations, hypergroups, strong regularity, the fundamental relation `β`/`β*`,
  complete parts, and the classical results surveyed in the paper's Section 5;
* `Hypergroups.Calibration` — the calibration proper: the relational and data formulations, the
  description operator, the selection interface, the bridges, witnessed hypergroups, and the
  non-degeneracy witnesses.

## Build and verify

```sh
elan toolchain install leanprover/lean4:v4.30.0   # if needed
lake update && lake exe cache get                 # fetch Mathlib (pinned to v4.30.0)
lake build
./scripts/verify.sh                               # rebuild + diff against logs/axioms.txt
```

`verify.sh` fails on any Lean error and on any difference from the recorded audit.

## Reading guide (paper → declaration)

| paper | declaration |
|---|---|
| relational form is axiom-free | `Calibration.groupModulo_of_stronglyRegular` |
| the choice locus | `Calibration.dataOfGroupModulo` |
| the bridge needs only a description operator | `Calibration.dataOfGroupModuloWithDescription` |
| the three selection families | `Calibration.GroupModuloSelections`, `selectionsOfDescription`, `dataOfSelections` |
| Lean's classical operator | `Calibration.classicalRDescription`, `dataOfGroupModulo_via_description` |
| data ⟹ quotient group | `Calibration.groupOfGroupModuloData` |
| witnessed ⟹ quotient group, choice-free | `Calibration.quotientGroupOfWitness` |
| non-degeneracy | `Calibration.prodW`, `prodW_multivalued`, `prodW_fstRel_stronglyRegular`, `prodW_quotient_classes_distinct`, `prodW_quotientEquiv`, `prodW_quotientEquiv_mul` |
| the survey table | the declarations of that name in `Hypergroups` |

## Notes

* No `sorry`, no `native_decide`, and no declaration whose conclusion is or contains `True`.
* No declaration depends on `sorryAx` or on Lean's compiler-trust axioms.
* Docstrings in `Hypergroups.Calibration` are in English. Those in the base namespace `Hypergroups`
  are in Japanese, the development language of the underlying library; declaration names and the
  audit output are language-independent.

## Use of AI assistance

Large language models were used substantially in preparing this development and the accompanying
paper: to search for the shape of the proofs, to write the Lean code, to draft the text, and to
check the literature; a further model was used as an adversarial reviewer. No AI system is an
author. Every axiom-footprint claim is the output of `#print axioms` on kernel-checked code, and
`scripts/verify.sh` lets anyone reproduce it; the surrounding interpretation is the author's.

## License

Apache-2.0, matching Mathlib.
