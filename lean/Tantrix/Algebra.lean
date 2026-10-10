import Tantrix.PhaseBudget

set_option autoImplicit false

/-!
# Integer bookkeeping and the Tantrix 136 upper bound

The general finite-phase inequality is in PhaseBudget. These lemmas
derive its interval hypotheses from toggles and congruences, restore
zero-triangle omissions, and specialize to 56 cells.
-/

namespace Tantrix

/-- The expression used in the final two budget cases. -/
def remainderBound (c d h : ℤ) : ℤ :=
  c ^ 2 + (9 - 4 * h) * c + 3 * d ^ 2 + (12 * h - 9) * d - 2 * h ^ 2

/-- The two-square identity for the area of a sorted six-direction word.
`Tantrix.Area.word_area_le_sorted` in DirectionOrder.lean supplies the
comparison with arbitrary closed words. -/
theorem sorted_area_certificate (a b c d : ℤ) :
    let p := a + c + (a + b - d)
    let q := b + d + (c + d - a)
    let s := a + b
    let t := c + d
    2 * areaNumerator p q - 18 * (2 * s * t - a ^ 2 - d ^ 2) =
      9 * (s - t) ^ 2 + 3 * (3 * (s + t) - 2 * (p + q)) ^ 2 := by
  dsimp [areaNumerator]
  ring

theorem sorted_area_bound (a b c d : ℤ) :
    9 * (2 * (a + b) * (c + d) - a ^ 2 - d ^ 2) ≤
      areaNumerator (a + c + (a + b - d)) (b + d + (c + d - a)) := by
  have h := sorted_area_certificate a b c d
  dsimp only at h
  nlinarith only [h, sq_nonneg (a + b - (c + d)),
    sq_nonneg (3 * (a + b + (c + d)) -
      2 * (a + c + (a + b - d) + (b + d + (c + d - a))))]

theorem area_perimeter_certificate (p q : ℤ) :
    3 * (p + q) ^ 2 - 2 * areaNumerator p q = (p - q) ^ 2 := by
  unfold areaNumerator
  ring

theorem area_perimeter_bound (p q : ℤ) :
    2 * areaNumerator p q ≤ 3 * (p + q) ^ 2 := by
  have h := area_perimeter_certificate p q
  nlinarith only [h, sq_nonneg (p - q)]

/-- Numerical counts for the two triangle groups in the written proof.
`Tantrix.Grid.constructedPhases` in Phases.lean constructs this record from
a maximum even network and proves all the constraints below.

Shaded triangles belong to the network's filling. Phase zero consists of
shaded upward and unshaded downward triangles; phase one is the complement
among occupied triangles. Shading is independent of the physical tile colours.

These counts set aside contacts beside no occupied triangle. If `b` counts
those forced omissions, the full boundary and omission budgets are
`L = P + 2*b` and `d = k + b`. -/
structure PhaseCounts where
  /-- Contacts beside exactly one occupied triangle: the triangle-region perimeter. -/
  P : ℤ
  /-- Omitted contacts beside at least one occupied triangle. -/
  k : ℤ
  /-- Omitted perimeter contacts. -/
  r : ℤ
  /-- Omitted internal contacts between two shaded triangles. -/
  a : ℤ
  /-- Omitted internal contacts between two unshaded triangles. -/
  w : ℤ
  /-- Retained perimeter contacts whose occupied triangle belongs to phase zero. -/
  x : ℤ
  /-- Omitted perimeter contacts whose occupied triangle belongs to phase zero. -/
  y : ℤ
  P_nonneg : 0 ≤ P
  r_nonneg : 0 ≤ r
  a_nonneg : 0 ≤ a
  w_nonneg : 0 ≤ w
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  x_le : x ≤ P - r
  y_le : y ≤ r
  omissions : k = r + a + w
  toggle_zero : a + w ≤ x - y
  toggle_one : a + w ≤ P - 2 * r - x + y
  divisible_zero : (x + a - (y + w)) % 3 = 0
  divisible_one : (P - r - x + a - (r - y + w)) % 3 = 0

/-- Retained minus omitted contacts on the boundary of phase zero. -/
def PhaseCounts.t (C : PhaseCounts) : ℤ := C.x - C.y - C.a - C.w
/-- The common remainder imposed by the two orientation counts modulo three. -/
def PhaseCounts.h (C : PhaseCounts) : ℤ := (-C.P - C.k) % 3

/-- The toggles and congruences put both phase surpluses and the common
imbalance inside the intervals required by the general two-phase bound. -/
theorem PhaseCounts.constraints (C : PhaseCounts) :
    0 ≤ C.k ∧ 0 ≤ C.t - C.h ∧
    0 ≤ C.P - 2 * C.k - C.h - C.t ∧
    0 ≤ C.a - C.h ∧ 0 ≤ C.h ∧ 0 ≤ C.P - 2 * C.k := by
  rcases C with ⟨P, k, r, a, w, x, y, hP, hr, ha, hw, hx, hy,
    hxP, hyr, hk, ht0, ht1, hm0, hm1⟩
  dsimp [PhaseCounts.t, PhaseCounts.h]
  omega

/-- The identified remainder and necessary feasibility conditions. -/
theorem PhaseCounts.remainder_conditions (C : PhaseCounts) :
    C.h = C.a % 3 ∧ C.h ≤ C.k ∧ 2 * C.h ≤ C.P - 2 * C.k := by
  have hsign := C.constraints
  rcases C with ⟨P, k, r, a, w, x, y, hP, hr, ha, hw, hx, hy,
    hxP, hyr, hk, ht0, ht1, hm0, hm1⟩
  dsimp [PhaseCounts.h, PhaseCounts.t] at hsign ⊢
  omega

/-- The detailed allocation data imply the simpler interval budgets. -/
theorem PhaseCounts.numerator_bound (C : PhaseCounts) :
    areaNumerator (C.x + C.a) (C.y + C.w) +
      areaNumerator (C.P - C.r - C.x + C.a) (C.r - C.y + C.w) ≤
      phaseNumerator C.P C.k C.h := by
  have hs := C.constraints
  have hk := C.omissions
  have hr := C.r_nonneg
  have hw := C.w_nonneg
  have hy := C.y_nonneg
  have hyr := C.y_le
  have h := two_phase_bound (C.P-2*C.k) C.k C.a C.h C.t
    (C.y+C.w) (C.r-C.y+C.w)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  dsimp only [PhaseCounts.t] at h
  convert h using 1 <;> congr 2 <;> omega

theorem PhaseCounts.area_bound (C : PhaseCounts) (F : ℤ)
    (harea : 9 * F ≤ areaNumerator (C.x + C.a) (C.y + C.w) +
      areaNumerator (C.P - C.r - C.x + C.a) (C.r - C.y + C.w)) :
    9 * F ≤ phaseNumerator C.P C.k C.h :=
  harea.trans C.numerator_bound

theorem bridge_certificate (P k b h : ℤ) :
    phaseNumerator (P + 2 * b) (k + b) h - phaseNumerator P k h =
      6 * b * (P + 2 * k + 2 * b) := by
  unfold phaseNumerator
  ring

theorem bridge_remainder (P k b : ℤ) :
    (-(P + 2 * b) - (k + b)) % 3 = (-P - k) % 3 := by
  omega

theorem bridge_bound (P k b : ℤ)
    (hP : 0 ≤ P) (hk : 0 ≤ k) (hb : 0 ≤ b) :
    phaseNumerator P k ((-P - k) % 3) ≤
      phaseNumerator (P + 2 * b) (k + b)
        ((-(P + 2 * b) - (k + b)) % 3) := by
  rw [bridge_remainder]
  have hid := bridge_certificate P k b ((-P - k) % 3)
  have hprod := mul_nonneg hb (show 0 ≤ P + 2 * k + 2 * b by omega)
  nlinarith only [hid, hprod]

theorem remainder_certificate (L d h : ℤ) :
    phaseNumerator L d h + 9 * L = remainderBound (L + d) d h := by
  unfold phaseNumerator remainderBound
  ring

theorem deficit_zero (c d : ℤ) :
    984 - remainderBound c d 0 =
      (27 - c) * (c + 36) + 3 * (4 - d) * (d + 1) := by
  unfold remainderBound
  ring

theorem deficit_two (c d : ℤ) :
    954 - remainderBound c d 2 =
      (28 - c) * (c + 29) + 3 * (5 - d) * (d + 10) := by
  unfold remainderBound
  ring

theorem case_zero (c d : ℤ) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (hc : c ≤ 27) (hd : d ≤ 4) : remainderBound c d 0 ≤ 984 := by
  have h1 := mul_nonneg (show 0 ≤ 27 - c by omega) (show 0 ≤ c + 36 by omega)
  have h2 := mul_nonneg (show 0 ≤ 4 - d by omega) (show 0 ≤ d + 1 by omega)
  nlinarith only [deficit_zero c d, h1, h2]

theorem case_two (c d : ℤ) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (hc : c ≤ 28) (hd : d ≤ 5) : remainderBound c d 2 ≤ 954 := by
  have h1 := mul_nonneg (show 0 ≤ 28 - c by omega) (show 0 ≤ c + 29 by omega)
  have h2 := mul_nonneg (show 0 ≤ 5 - d by omega) (show 0 ≤ d + 10 by omega)
  nlinarith only [deficit_two c d, h1, h2]

/-- The remainder correction only lowers the relaxed bound when c ≥ 3d. -/
theorem remainder_le_zero (c d h : ℤ) (hcd : 0 ≤ c - 3 * d) (hh : 0 ≤ h) :
    remainderBound c d h ≤ remainderBound c d 0 := by
  have hp := mul_nonneg hcd hh
  unfold remainderBound
  nlinarith [sq_nonneg h]

/-- The final two-case arithmetic: `F` counts triangles, `L` is the boundary
budget, `d` is the omission budget, and `m` is the score.
GeometryApplication.lean supplies the counting identities and area estimates
for a connected support; Disconnected.lean supplies the adjusted budgets
for a support with several components. -/
theorem score_le_136_of_estimates (F L d m : ℤ)
    (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hcount : F + L = 110) (hscore : m + L + d = 165)
    (hwhole : 6 * F ≤ L ^ 2)
    (hphase : 9 * F ≤ phaseNumerator L d ((-L - d) % 3)) :
    m ≤ 136 := by
  by_contra hbad
  have hc : L + d ≤ 28 := by omega
  have hL23 : 23 ≤ L := by
    by_contra hsmall
    have hL22 : L ≤ 22 := by omega
    have hprod := mul_nonneg hL (show 0 ≤ 22 - L by omega)
    nlinarith only [hprod, hL22, hwhole, hcount]
  have hc0 : 0 ≤ L + d := by omega
  have hM : 990 ≤ remainderBound (L + d) d ((-L - d) % 3) := by
    rw [← remainder_certificate]
    omega
  by_cases hc27 : L + d ≤ 27
  · have hd4 : d ≤ 4 := by omega
    have hrelax := remainder_le_zero (L + d) d ((-L - d) % 3)
      (by omega) (by omega)
    have hu := case_zero (L + d) d hc0 hd hc27 hd4
    omega
  · have heq : L + d = 28 := by omega
    have hr : (-L - d) % 3 = 2 := by omega
    rw [hr] at hM
    have hu := case_two (L + d) d hc0 hd hc (by omega)
    omega

/-- Combine the phase-area estimates with the exact 56-cell counts, restoring
the `b` forced omissions. `Tantrix.Grid.score_le_136_of_directed_area` in
GeometryApplication.lean constructs `C` and supplies these hypotheses;
`Tantrix.Grid.score_le_136` supplies the proved directed area bound. -/
theorem score_le_136_of_phase_data (C : PhaseCounts) (F b m : ℤ)
    (hb : 0 ≤ b)
    (hcount : F + (C.P + 2 * b) = 110)
    (hscore : m + (C.P + 2 * b) + (C.k + b) = 165)
    (hwhole : 6 * F ≤ (C.P + 2 * b) ^ 2)
    (harea : 9 * F ≤ areaNumerator (C.x + C.a) (C.y + C.w) +
      areaNumerator (C.P - C.r - C.x + C.a) (C.r - C.y + C.w)) :
    m ≤ 136 := by
  have hk := C.constraints.1
  have hL : 0 ≤ C.P + 2 * b := by have := C.P_nonneg; omega
  have hd : 0 ≤ C.k + b := by omega
  have hphase := (C.area_bound F harea).trans
    (bridge_bound C.P C.k b C.P_nonneg hk hb)
  exact score_le_136_of_estimates F (C.P + 2 * b) (C.k + b) m
    hL hd hcount hscore hwhole hphase

end Tantrix
