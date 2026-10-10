import Tantrix.DirectionOrder
import Tantrix.AreaExamples

set_option autoImplicit false

namespace Tantrix.Area

/-- Regression checks include the empty word, a cyclically shifted
triangle, a clockwise triangle, a zero-area reversal, a repeated closed triangle, and a
concatenation with both orientations. The general theorem supplies the
inequality; only the concrete closure checks use computation. -/
theorem closed_word_regressions :
    ∀ w ∈ ([[],[2,4,0],[1,5,3],[3,0],[0,2,4,0,2,4],[0,2,4,1,5,3]] : List (List (Fin 6))),
      9 * wordArea (w.map direction) ≤ Tantrix.areaNumerator (upSteps w) (downSteps w) := by
  intro w hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact closed_word_area_bound _ (by decide)

/-- The two-swap argument rejects a closed word containing
the backward jump 5 to 1 while direction 0 is present. -/
theorem skipped_direction_not_maximum :
    ¬ IsAreaMaximum direction [0,5,1,3,3] := by
  intro h
  exact maximum_no_skipped_step direction 5 1 0 [] [3,3]
    h (by decide) (by decide)

/-- Sorting covers empty, zero-area, positive-area and negative-area words. -/
theorem sorting_regressions :
    ∀ w ∈ ([[],[3,0],[2,4,0],[1,5,3]] : List (List (Fin 6))),
      areaOf direction w ≤ areaOf direction (sortedDirections w) := by
  intro w hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;>
    exact word_area_le_sorted _ (by decide)

/-- The stronger no-skipped-step lemma also works without closure. -/
theorem skipped_direction_open_not_maximum :
    ¬ IsAreaMaximum direction [0,5,1] := by
  intro h
  exact maximum_no_skipped_step direction 5 1 0 [] [] h (by decide) (by decide)

/-- Negative control: closure is essential. This open three-step word
would violate the claimed area bound if the closure hypothesis were dropped. -/
theorem open_word_violates_bound :
    let w : List (Fin 6) := [0,1,2]
    displacement (w.map direction) ≠ 0 ∧
      Tantrix.areaNumerator (upSteps w) (downSteps w) < 9 * wordArea (w.map direction) := by decide

end Tantrix.Area

namespace Tantrix.Grid

/-- The elementary-triangle model satisfies the area inequality by direct
application of the general theorem. -/
theorem unitTriangle_area_from_general : DirectedAreaBound unitTriangleSupport :=
  directed_area_bound unitTriangleSupport

end Tantrix.Grid
