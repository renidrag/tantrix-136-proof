# Read and verify the Lean proof

The final theorem is `Tantrix.Loops.full_set_optimum_136` in
[ColouredSharpness.lean](Tantrix/ColouredSharpness.lean). It combines the
upper bound with the 56-tile construction scoring 136. The
[loop model](Tantrix/PhysicalLoops.lean) and
[numbered inventory](Tantrix/TileInventory.lean) specify the puzzle rules.

## Reading guide

Start with the [written proof](../proof.md) for the mathematical argument.
The table follows its order and gives the main Lean statements to look for.
Theorem names below omit the common `Tantrix.` prefix.

| Step in the written proof | Lean files and main statements |
|---|---|
| [1. Loops become an even network, preserving the score](../proof.md#1-the-geometric-problem) | [PhysicalLoops.lean](Tantrix/PhysicalLoops.lean): `Loops.to_even_network` |
| [1. Triangle fillings and exact contact counts](../proof.md#1-the-geometric-problem) | [Grid.lean](Tantrix/Grid.lean): `Grid.boundary_bijective`; [Counting.lean](Tantrix/Counting.lean): `Grid.counting_56` |
| [2. Switching a region's boundary cannot improve a maximum network](../proof.md#2-area-and-maximality) | [Boundary.lean](Tantrix/Boundary.lean): `Grid.maximum_boundary_toggle` |
| [2. The directed area bound](../proof.md#2-area-and-maximality) | [DirectionOrder.lean](Tantrix/DirectionOrder.lean): `Grid.directed_area_bound` |
| [3. The two triangle groups and their combined area estimate](../proof.md#3-a-common-budget-for-the-two-phases) | [Phases.lean](Tantrix/Phases.lean): `Grid.exists_phase_data`; [Algebra.lean](Tantrix/Algebra.lean): `PhaseCounts.area_bound` |
| [4. The final arithmetic and connected upper bound](../proof.md#4-two-budget-cases-finish-the-proof) | [Algebra.lean](Tantrix/Algebra.lean): `score_le_136_of_estimates`; [GeometryApplication.lean](Tantrix/GeometryApplication.lean): `Grid.score_le_136` |
| [5. Allowing disconnected arrangements](../proof.md#5-disconnected-supports) | [Disconnected.lean](Tantrix/Disconnected.lean): `Grid.score_le_136_of_no_holes` and `Loops.score_le_136_of_no_holes` |
| [The construction attaining 136 and the exact optimum](../proof.md#4-two-budget-cases-finish-the-proof) | [ColouredSharpness.lean](Tantrix/ColouredSharpness.lean): `Loops.Coloured136.certificate` and `Loops.full_set_optimum_136` |

For the area bound, [BoundaryWalks.lean](Tantrix/BoundaryWalks.lean) turns
triangle boundaries into closed direction words (`Grid.region_boundary_word`).
DirectionOrder.lean proves their area estimate. For the two-group calculation,
[PhaseBudget.lean](Tantrix/PhaseBudget.lean) supplies `two_phase_bound`;
Algebra.lean derives its hypotheses from the actual counts.

The two triangle groups are called **phases** in the code. Their counting
letters are explained beside `PhaseCounts` in Algebra.lean. In Counting.lean,
`perimeterCount`, `bareCount` and `boundaryCount` are the written proof's
`P`, `b` and `L = P + 2b`. Lean uses `S` for the set of occupied cells;
the main README uses the same letter for the number of exposed tile sides.

## Puzzle rules in the model

The definitions to compare with the [puzzle rules](../README.md#the-puzzle) are:

- [TileInventory.lean](Tantrix/TileInventory.lean): `Inventory.UsesFullSet`
  requires each numbered tile once, with a rotation matching all six side
  colours. Each colour present on a tile has two endpoints, which fixes its strand.
- [PhysicalLoops.lean](Tantrix/PhysicalLoops.lean): `Placement` requires
  matching across every contact; `LoopTrace` follows a closed monochromatic
  loop once; `score` adds visited-tile counts separately for each colour.
- [Grid.lean](Tantrix/Grid.lean): `NoHoles` requires every empty cell to
  escape every finite box through empty neighbouring cells.

`ScoredLoops` permits any chosen loop of each colour, or an empty trace
contributing zero. The upper bound covers every choice, including the longest
loops. The certificate supplies four nonempty loops totalling 136. Thus the
final `IsGreatest` statement establishes both attainability and the upper bound
needed for the puzzle's longest-loop scoring rule.

## First run

Use a Bash shell with Git and [Elan](https://leanprover-community.github.io/install/project.html)
available. Elan selects the pinned Lean version from `lean-toolchain`.
From the package root, fetch the required precompiled Mathlib modules and
run the checks:

```sh
cd lean
env LEAN_NUM_THREADS=1 RAYON_NUM_THREADS=1 lake exe cache get \
  Mathlib.Tactic.Ring Mathlib.Tactic.Linarith \
  Mathlib.Data.ZMod.Basic Mathlib.Data.Int.Interval \
  Mathlib.Algebra.BigOperators.Intervals \
  Mathlib.LinearAlgebra.Matrix.Rank Mathlib.Algebra.Field.ZMod \
  Mathlib.FieldTheory.Finiteness Mathlib.Tactic.FinCases \
  Mathlib.Data.List.Basic Mathlib.Algebra.Group.Prod \
  Mathlib.Data.Fin.VecNotation Mathlib.Data.List.Lex \
  Mathlib.Data.List.Permutation Mathlib.Data.Finset.Max \
  Mathlib.Data.List.Perm.Basic Mathlib.Algebra.Order.BigOperators.Group.List \
  Mathlib.Algebra.Order.BigOperators.Ring.Finset
bash verify.sh
```

For later runs, from the package root:

```sh
bash lean/verify.sh
```

The script builds with one Lean worker, treats warnings as errors and runs
all 244 guarded dependency checks in [Audit.lean](Audit.lean). A failed
build or audit produces a nonzero exit status. The permitted foundations
are `propext`, `Classical.choice` and `Quot.sound`.

## GitHub verification

The [GitHub Actions workflow](../.github/workflows/verify.yml) runs on pushes,
pull requests and manual requests. It checks the source checksums, builds the
proof with the pinned dependencies and runs the same 244 dependency guards.
It then uses Lean's bundled `leanchecker` to recheck the compiled `Tantrix`
declarations with the kernel. To run that additional check locally after a
successful build, from this directory:

```sh
LEAN_NUM_THREADS=1 lake env leanchecker -v Tantrix
```

## Versions and source

- Lean **4.34.1**, pinned in [lean-toolchain](lean-toolchain).
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, pinned in
  [lakefile.toml](lakefile.toml).
- All dependency revisions are recorded in [lake-manifest.json](lake-manifest.json).

Keep these pins when reproducing the result; no dependency update is needed.
Downloaded dependencies and build output go in the ignored `.lake/` directory.

The 10 October 2026 source snapshot is identified by [SHA256SUMS](SHA256SUMS).
Every listed file is an unchanged copy of the checked source. The example
files are included because the existing audit checks them too.
The written proof is an edited presentation of the same argument.
