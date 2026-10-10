import Tantrix.GeneralBounds
import Tantrix.AreaExamples

set_option autoImplicit false
open scoped BigOperators

namespace Tantrix

/-- The finite theorem includes an empty family. -/
theorem empty_phase_example : (0 : ℤ) ≤ 0 := by
  exact finite_phase_bound (∅ : Finset Unit) (0 : ℤ) 0 0
    (fun _ => 0) (fun _ => 0) (by omega) (by omega)
    (by simp) (by simp) (by simp)

/-- Three phases with rational (not necessarily integer) budgets.
The theorem covers every such allocation, not just a numerical sample. -/
theorem three_phase_rational_bound (t q : Fin 3 → ℚ)
    (ht : ∀ i, (1/2 : ℚ) ≤ t i)
    (hq : ∀ i, 0 ≤ q i) (hqk : ∀ i, q i ≤ (1/2 : ℚ))
    (hsum : ∑ i, t i = 3) :
    (∑ i, areaNumerator (t i+1+q i) (q i)) ≤ 36 := by
  have hb := finite_phase_bound Finset.univ (1 : ℚ) (1/2) (1/2) t q
    (by norm_num) (by rfl) (by intro i _; exact ht i)
    (by intro i _; exact hq i) (by intro i _; linarith [hqk i])
  norm_num [hsum] at hb
  exact hb

/-- Concentrated excess attains the three-phase bound in integer data. -/
theorem three_phase_sharp_example :
    (∑ i : Fin 3, areaNumerator (if i=0 then (7 : ℤ) else 4) 1) = 144 := by
  have h := finite_phase_sharp Finset.univ (0 : Fin 3) (by simp) (6 : ℤ) 2 1
  convert h using 1 <;> norm_num [Fin.sum_univ_succ,areaNumerator]

/-- Negative control: permitting a negative surplus breaks the bound. -/
theorem negative_surplus_breaks_bound :
    phaseNumerator (2 : ℤ) 1 0 <
      areaNumerator (1+1 : ℤ) 1 + areaNumerator (-1+1 : ℤ) 1 := by
  norm_num [phaseNumerator,areaNumerator]

/-- Negative control: the smaller-count cap is also necessary. -/
theorem uncapped_count_breaks_bound :
    phaseNumerator (2 : ℤ) 1 0 <
      areaNumerator (2 : ℤ) 2 + areaNumerator (0 : ℤ) 0 := by
  norm_num [phaseNumerator,areaNumerator]

/-- The all-size numerical conditions remain consistent at score 136.
This is a numerical witness, not a certified lattice placement. -/
theorem budget_136_consistent : BudgetEstimates 56 28 1 := by
  constructor <;> norm_num [phaseNumerator]

end Tantrix

namespace Tantrix.Grid

/-- A genuine three-cell support supplies its budget through the general theorem. -/
theorem unitTriangle_budget_example : Tantrix.BudgetEstimates 3 3 0 := by
  let x := boundaryVector unitTriangleSupport (fun _ => 1)
  have hb := (maximum_budget unitTriangleSupport unitTriangle_connected
    unitTriangle_no_holes x unitTriangle_full_maximum).1
  have hs := region_boundary_count unitTriangleSupport (fun _ => 1)
  rw [unitTriangle_directed_counts.2.1,unitTriangle_directed_counts.2.2] at hs
  have hsel := selection_partition unitTriangleSupport x
  have he := unitTriangle_counts.2.1
  have hd : omittedCount unitTriangleSupport x = 0 := by
    dsimp only [x] at hsel ⊢
    omega
  have hv : unitTriangleSupport.card = 3 := unitTriangle_counts.1
  simpa [hv,unitTriangle_counts.2.2.2,hd] using hb

/-- The generalized budget interface recovers the existing 56-cell theorem. -/
theorem score_le_136_via_budgets (S : Support) (hc : Connected S) (hn : NoHoles S)
    (h56 : S.card = 56) (x : Contacts S → Bit) (he : (decodeEdges S x).Even) :
    selectedCount S x ≤ 136 := by
  apply score_le_of_budget_bound S hc hn 136 ?_ x he
  intro L d hb
  exact Tantrix.score_le_136_of_estimates (2*(S.card : ℤ)-2-L) L d
    (3*(S.card : ℤ)-3-L-d) hb.boundary_nonneg hb.omissions_nonneg
    (by rw [h56]; omega) (by rw [h56]; omega) hb.whole_area hb.phase_area

end Tantrix.Grid
