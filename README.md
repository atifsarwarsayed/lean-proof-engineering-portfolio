# Lean Proof Engineering Portfolio

Selected Lean 4 projects exploring formalisation in metric geometry and
algebraic topology.

## Projects

### 1. Hausdorff distance and pseudo-metric structure

**File:** `LeanProofEngineeringPortfolio/GromovHausdorff.lean`

Develops definitions for neighbourhoods of subsets of a metric space and a
Hausdorff-style distance. The file includes lemmas on containment,
symmetry, and the triangle inequality, and attempts to equip the set of
subsets with a `PseudoMetricSpace` structure.

**Status:** Work in progress. The triangle inequality proof contains an
unfinished `sorry`; the resulting pseudo-metric construction should not be
regarded as fully verified.

### 2. No-retraction and Brouwer fixed-point arguments on the 2-disc

**File:** `LeanProofEngineeringPortfolio/FixedPointDimension2.lean`

Formalises the closed unit disc and unit circle as subtypes of Euclidean
space. The development explores path-connectedness, contractibility,
fundamental groups, the no-retraction theorem, and a route towards
Brouwer's fixed-point theorem in dimension two.

**Status:** Work in progress. Several proof obligations remain unfinished,
including arguments involving fundamental groups, a ray intersecting the
unit circle, and continuity of a constructed retraction. The file does not
currently establish a complete formal proof of Brouwer's fixed-point theorem.

## Toolchain

- Lean 4.26.0
- Mathlib v4.26.0

The project configuration and dependency manifest record the intended
toolchain and dependencies. Compilation has not been verified as part of
preparing this portfolio.

## Purpose

These projects reflect ongoing work in Lean 4, including the representation
of mathematical objects, proof decomposition, use of Mathlib, and the
formalisation of results in topology and metric geometry.
