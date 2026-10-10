import Tantrix.Counting
import Tantrix.Algebra
import Tantrix.Phases
import Tantrix.BoundaryWalks
import Tantrix.DirectionOrder

/-!
# Assembling the connected geometric upper bound

`score_le_136` combines the lattice counts, maximum-network phases and
proved directed area inequality. The intermediate statements expose these
inputs separately; the final theorem supplies them all.
Disconnected.lean extends the bound to supports with several components,
and ColouredSharpness.lean combines it with the full-set coloured construction.
-/

set_option autoImplicit false

namespace Tantrix.Grid

/-- Apply the numerical bound to lattice counts, given compatible phase data
and two area estimates. `score_le_136_of_directed_area` supplies the phase
data and derives the whole-area estimate from the directed area bound. -/
theorem score_le_136_of_geometric_phase_data (S : Support)
    (hc : Connected S) (hn : NoHoles S) (h56 : S.card = 56)
    (x : Contacts S → Bit) (C : Tantrix.PhaseCounts)
    (hP : C.P = (perimeterCount S : ℤ))
    (hk : C.k + (bareCount S : ℤ) = (omittedCount S x : ℤ))
    (hwhole : 6 * (triangleCount S : ℤ) ≤ (boundaryCount S : ℤ)^2)
    (harea : 9 * (triangleCount S : ℤ) ≤
      Tantrix.areaNumerator (C.x+C.a) (C.y+C.w) +
      Tantrix.areaNumerator (C.P-C.r-C.x+C.a) (C.r-C.y+C.w)) :
    selectedCount S x ≤ 136 := by
  have hcounts := counting_56 S hc hn h56 x
  have hL : C.P + 2 * (bareCount S : ℤ) = (boundaryCount S : ℤ) := by
    simp [boundaryCount,hP]
  have h := Tantrix.score_le_136_of_phase_data C (triangleCount S) (bareCount S)
    (selectedCount S x) (Int.natCast_nonneg _) (by rw [hL]; omega)
    (by rw [hL,hk]; omega) (by rwa [hL]) harea
  omega

/-- The ordinary area estimate follows from the same directed estimate
used for the phases; it is not a separate geometric assumption. -/
theorem whole_area_of_directed (S : Support) (ha : DirectedAreaBound S) :
    6 * (triangleCount S : ℤ) ≤ (boundaryCount S : ℤ)^2 := by
  have h := ha (fun _ => 1)
  rw [whole_regionArea] at h
  have hp := region_boundary_count S (fun _ => 1)
  rw [whole_boundary_count] at hp
  have hg := Tantrix.area_perimeter_bound
    (directedUp S (fun _ => 1)) (directedDown S (fun _ => 1))
  rw [hp] at hg
  have hsmall : 6 * (triangleCount S : ℤ) ≤ (perimeterCount S : ℤ)^2 := by omega
  have hnonneg : 0 ≤ (perimeterCount S : ℤ) := Int.natCast_nonneg _
  have hbare : 0 ≤ (bareCount S : ℤ) := Int.natCast_nonneg _
  have hprod := mul_nonneg hnonneg hbare
  have hsq := sq_nonneg (bareCount S : ℤ)
  simp only [boundaryCount,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith

/-- The connected 56-cell upper bound with the directed area estimate as
an explicit input. Filling, counting and phase data are derived here.
`score_le_136` below supplies the proved area estimate. -/
theorem score_le_136_of_directed_area (S : Support)
    (hc : Connected S) (hn : NoHoles S) (h56 : S.card = 56)
    (ha : DirectedAreaBound S) (x : Contacts S → Bit)
    (he : (decodeEdges S x).Even) : selectedCount S x ≤ 136 := by
  obtain ⟨y,hy⟩ := exists_maximum S
  obtain ⟨C,hP,hk,harea⟩ := exists_phase_data S hn y hy
  have hb := score_le_136_of_geometric_phase_data S hc hn h56 y C hP hk
    (whole_area_of_directed S ha) (harea ha)
  exact (hy.2 x he).trans hb

/-- Transfer the closed six-direction word bound to triangle regions and
apply the connected upper bound. `score_le_136` supplies the word inequality
proved in DirectionOrder.lean. -/
theorem score_le_136_of_closed_word_bound
    (ha : Tantrix.Area.ClosedWordAreaBound) (S : Support)
    (hc : Connected S) (hn : NoHoles S) (h56 : S.card = 56)
    (x : Contacts S → Bit) (he : (decodeEdges S x).Even) :
    selectedCount S x ≤ 136 :=
  score_le_136_of_directed_area S hc hn h56 (directed_area_of_closed_word_bound ha S) x he

/-- The connected, hole-free 56-cell geometric upper bound. Every even
contact subset has at most 136 selected edges. All area, filling, counting
and phase facts are derived from the explicit model; no extra geometric
inequality or phase certificate is assumed. -/
theorem score_le_136 (S : Support)
    (hc : Connected S) (hn : NoHoles S) (h56 : S.card = 56)
    (x : Contacts S → Bit) (he : (decodeEdges S x).Even) :
    selectedCount S x ≤ 136 :=
  score_le_136_of_closed_word_bound Tantrix.Area.closed_word_area_bound S hc hn h56 x he

end Tantrix.Grid
