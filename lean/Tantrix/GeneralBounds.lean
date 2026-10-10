import Tantrix.GeometryApplication

/-!
# Necessary bounds for every support size

The phase estimate needs no connectedness or prescribed tile count.
Connected counting turns it into numerical budgets for arbitrary n.
These are necessary conditions, not a claim that every budget is realizable.
-/

set_option autoImplicit false

namespace Tantrix

/-- Necessary numerical conditions for a maximum network on n cells.
This is not a definition of a permitted support or a sufficiency theorem. -/
structure BudgetEstimates (n L d : ℤ) : Prop where
  boundary_nonneg : 0 ≤ L
  omissions_nonneg : 0 ≤ d
  triangle_nonneg : 0 ≤ 2*n-2-L
  score_nonneg : 0 ≤ 3*n-3-L-d
  whole_area : 6*(2*n-2-L) ≤ L^2
  remainder_le : (-L-d)%3 ≤ d
  remainder_space : 2*((-L-d)%3) ≤ L-2*d
  phase_area : 9*(2*n-2-L) ≤ phaseNumerator L d ((-L-d)%3)

end Tantrix

namespace Tantrix.Grid

/-- The restored phase bounds hold for any finite hole-free support,
including disconnected supports, with no fixed tile count. -/
theorem maximum_phase_estimates (S : Support) (hn : NoHoles S)
    (x : Contacts S → Bit) (hm : IsMaximum S x) :
    let L : ℤ := boundaryCount S
    let d : ℤ := omittedCount S x
    let h := (-L-d)%3
    h ≤ d ∧ 2*h ≤ L-2*d ∧
      9*(triangleCount S : ℤ) ≤ Tantrix.phaseNumerator L d h := by
  obtain ⟨C,hP,hk,ha⟩ := exists_phase_data S hn x hm
  have hb : 0 ≤ (bareCount S : ℤ) := Int.natCast_nonneg _
  have hL : (boundaryCount S : ℤ) = C.P + 2*(bareCount S : ℤ) := by
    simp [boundaryCount,hP]
  have hrem := Tantrix.bridge_remainder C.P C.k (bareCount S)
  have hphase := (C.area_bound (triangleCount S) (ha (directed_area_bound S))).trans
    (Tantrix.bridge_bound C.P C.k (bareCount S) C.P_nonneg C.constraints.1 hb)
  rw [hrem] at hphase
  have hc := C.remainder_conditions
  dsimp only [Tantrix.PhaseCounts.h] at hc
  dsimp only
  rw [hL,← hk,hrem]
  exact ⟨by omega,by omega,hphase⟩

/-- Every actual maximum on a connected hole-free support satisfies the
budget inequalities, and its score is 3n-3-L-d. No value of n is fixed. -/
theorem maximum_budget (S : Support) (hc : Connected S) (hn : NoHoles S)
    (x : Contacts S → Bit) (hm : IsMaximum S x) :
    Tantrix.BudgetEstimates (S.card : ℤ) (boundaryCount S) (omittedCount S x) ∧
      (selectedCount S x : ℤ) =
        3*(S.card : ℤ)-3-(boundaryCount S : ℤ)-(omittedCount S x : ℤ) := by
  have hcount := support_counting S hc hn
  dsimp only [vertexCount] at hcount
  have hsel := selection_partition S x
  have hF : (triangleCount S : ℤ) = 2*(S.card : ℤ)-2-(boundaryCount S : ℤ) := by omega
  have hscore : (selectedCount S x : ℤ) =
      3*(S.card : ℤ)-3-(boundaryCount S : ℤ)-(omittedCount S x : ℤ) := by omega
  obtain ⟨hr,hs,hphase⟩ := maximum_phase_estimates S hn x hm
  refine ⟨{
    boundary_nonneg := Int.natCast_nonneg _
    omissions_nonneg := Int.natCast_nonneg _
    triangle_nonneg := ?_
    score_nonneg := ?_
    whole_area := ?_
    remainder_le := hr
    remainder_space := hs
    phase_area := ?_ },hscore⟩
  · rw [← hF]; exact Int.natCast_nonneg _
  · rw [← hscore]; exact Int.natCast_nonneg _
  · rw [← hF]; exact whole_area_of_directed S (directed_area_bound S)
  · rwa [← hF]

/-- A bound proved for all numerical budgets bounds every even network.
Geometry is discharged here once, for every support size and every bound. -/
theorem score_le_of_budget_bound (S : Support) (hc : Connected S) (hn : NoHoles S)
    (B : ℕ)
    (hB : ∀ L d : ℤ, Tantrix.BudgetEstimates (S.card : ℤ) L d →
      3*(S.card : ℤ)-3-L-d ≤ (B : ℤ))
    (x : Contacts S → Bit) (he : (decodeEdges S x).Even) :
    selectedCount S x ≤ B := by
  obtain ⟨y,hy⟩ := exists_maximum S
  obtain ⟨hb,hscore⟩ := maximum_budget S hc hn y hy
  have hbound := hB _ _ hb
  rw [← hscore] at hbound
  have hnat : selectedCount S y ≤ B := by exact_mod_cast hbound
  exact (hy.2 x he).trans hnat

end Tantrix.Grid
