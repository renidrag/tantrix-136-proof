import Tantrix.Algebra

set_option autoImplicit false

/-!
# A sharp numerical instance

This demonstrates that the conditional theorem's premises are consistent
at score 136. It is not a formalized lattice support or coloured placement.
-/

namespace Tantrix

def sharpPhaseCounts : PhaseCounts where
  P := 28
  k := 1
  r := 0
  a := 1
  w := 0
  x := 2
  y := 0
  P_nonneg := by norm_num
  r_nonneg := by norm_num
  a_nonneg := by norm_num
  w_nonneg := by norm_num
  x_nonneg := by norm_num
  y_nonneg := by norm_num
  x_le := by norm_num
  y_le := by norm_num
  omissions := by norm_num
  toggle_zero := by norm_num
  toggle_one := by norm_num
  divisible_zero := by norm_num
  divisible_one := by norm_num

/-- A single witness for all premises, with F=82, b=0 and score=136. -/
theorem sharp_numerical_witness :
    ∃ (C : PhaseCounts) (F b m : ℤ),
      m = 136 ∧ 0 ≤ b ∧
      F + (C.P + 2 * b) = 110 ∧
      m + (C.P + 2 * b) + (C.k + b) = 165 ∧
      6 * F ≤ (C.P + 2 * b) ^ 2 ∧
      9 * F ≤ areaNumerator (C.x + C.a) (C.y + C.w) +
        areaNumerator (C.P - C.r - C.x + C.a) (C.r - C.y + C.w) := by
  refine ⟨sharpPhaseCounts, 82, 0, 136, ?_⟩
  norm_num [sharpPhaseCounts, areaNumerator]

end Tantrix
