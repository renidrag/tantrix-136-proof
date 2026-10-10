import Tantrix.Regions

/-!
# Phase data from an actual maximum even network

The two phases come from its finite triangle filling and triangle
orientation. Local edge identities have only nine cases: absent, white or
black on each side. The toggle inequalities are derived from maximality,
not included as assumptions about a colouring.

Phase zero groups shaded upward triangles with unshaded downward triangles;
phase one contains the other occupied triangles. Across a retained internal
contact both shading and orientation change, preserving the phase. Across
an omitted internal contact only orientation changes, separating the phases.
The resulting counts populate `Tantrix.PhaseCounts`, documented in Algebra.lean.
-/

set_option autoImplicit false
open scoped BigOperators
open Classical
noncomputable section

namespace Tantrix.Grid

namespace PhaseLocal

/-- `none` is an absent triangle; `some 0` is occupied and unshaded;
`some 1` is occupied and shaded. The two arguments below are the upward
and downward triangles at a contact, respectively. -/
abbrev Label := Option Bit
def flip (u : Label) : Label := u.map (fun z => 1-z)
def value (u : Label) : Bit := u.getD 0
def network (u v : Label) : Bit := value u + value v
def zeroBoundary (u v : Label) : Bit := value u + value (flip v)
def oneBoundary (u v : Label) : Bit := value (flip u) + value v
def bare (u v : Label) : ℤ := if u = none ∧ v = none then 1 else 0
def perimeter (u v : Label) : ℤ := if u.isSome ≠ v.isSome then 1 else 0
def r (u v : Label) : ℤ := if u.isSome ≠ v.isSome ∧ network u v = 0 then 1 else 0
def a (u v : Label) : ℤ := if u = some 1 ∧ v = some 1 then 1 else 0
def w (u v : Label) : ℤ := if u = some 0 ∧ v = some 0 then 1 else 0
def x (u v : Label) : ℤ := if u = some 1 ∧ v = none then 1 else 0
def y (u v : Label) : ℤ := if u = none ∧ v = some 0 then 1 else 0
def directed (u v : Label) : ℤ := if value u ≠ 0 ∧ value v = 0 then 1 else 0
def gained (n t : Bit) : ℤ := if t ≠ 0 ∧ n = 0 then 1 else 0
def lost (n t : Bit) : ℤ := if t ≠ 0 ∧ n ≠ 0 then 1 else 0

/-- All possible local incidences, proved by kernel reduction of nine cases. -/
theorem table (u v : Label) :
    (if network u v = 0 then (1 : ℤ) else 0) = bare u v + r u v + a u v + w u v ∧
    directed u (flip v) = x u v + a u v ∧
    directed (flip v) u = y u v + w u v ∧
    directed v (flip u) = perimeter u v - r u v - x u v + a u v ∧
    directed (flip u) v = r u v - y u v + w u v ∧
    gained (network u v) (zeroBoundary u v) = a u v + w u v + y u v ∧
    lost (network u v) (zeroBoundary u v) = x u v ∧
    gained (network u v) (oneBoundary u v) = a u v + w u v + r u v - y u v ∧
    lost (network u v) (oneBoundary u v) = perimeter u v - r u v - x u v ∧
    x u v ≤ perimeter u v - r u v ∧ y u v ≤ r u v := by
  cases u with
  | none => cases v with
    | none => decide
    | some v => fin_cases v <;> decide
  | some u =>
    fin_cases u <;> cases v with
    | none => decide
    | some v => fin_cases v <;> decide

end PhaseLocal

def triangleLabel (S : Support) (r : Triangles S → Bit) (t : TriangleIndex) : PhaseLocal.Label :=
  if h : trianglePresent S t then some (r ⟨t,h⟩) else none

theorem triangleLabel_value (S : Support) (r : Triangles S → Bit) (t : TriangleIndex) :
    PhaseLocal.value (triangleLabel S r t) = extend r t := by
  unfold triangleLabel extend; split_ifs <;> rfl

/-- Shaded upward and unshaded downward triangles. Here `r` is the filling
labelling, rather than the numerical omission count `Tantrix.PhaseCounts.r`. -/
def phaseZero (S : Support) (r : Triangles S → Bit) : Triangles S → Bit :=
  fun t => if t.val.1 then 1-r t else r t
/-- The complementary group: unshaded upward and shaded downward triangles. -/
def phaseOne (S : Support) (r : Triangles S → Bit) : Triangles S → Bit :=
  fun t => if t.val.1 then r t else 1-r t

def phaseSum (S : Support) (r : Triangles S → Bit)
    (f : PhaseLocal.Label → PhaseLocal.Label → ℤ) : ℤ :=
  ∑ e : Contacts S, f (triangleLabel S r (upAt e.val)) (triangleLabel S r (downAt e.val))

theorem phaseSum_add (S : Support) (r : Triangles S → Bit)
    (f g : PhaseLocal.Label → PhaseLocal.Label → ℤ) :
    phaseSum S r (fun u v => f u v + g u v) = phaseSum S r f + phaseSum S r g :=
  Finset.sum_add_distrib

theorem phaseSum_sub (S : Support) (r : Triangles S → Bit)
    (f g : PhaseLocal.Label → PhaseLocal.Label → ℤ) :
    phaseSum S r (fun u v => f u v - g u v) = phaseSum S r f - phaseSum S r g :=
  Finset.sum_sub_distrib _ _

theorem phaseSum_nonneg (S : Support) (r : Triangles S → Bit)
    (f : PhaseLocal.Label → PhaseLocal.Label → ℤ) (hf : ∀ u v, 0 ≤ f u v) :
    0 ≤ phaseSum S r f := Finset.sum_nonneg (fun _ _ => hf _ _)

theorem phase_boundary_labels (S : Support) (r : Triangles S → Bit) (e : Contacts S) :
    boundaryVector S r e = PhaseLocal.network
      (triangleLabel S r (upAt e.val)) (triangleLabel S r (downAt e.val)) := by
  simp [boundaryVector,boundary_edgeValue,triangleValue_decode,PhaseLocal.network,triangleLabel_value]

theorem phase_zero_labels (S : Support) (r : Triangles S → Bit) (e : Contacts S) :
    upLabel S (phaseZero S r) e = PhaseLocal.value (triangleLabel S r (upAt e.val)) ∧
    downLabel S (phaseZero S r) e = PhaseLocal.value (PhaseLocal.flip (triangleLabel S r (downAt e.val))) := by
  constructor
  · simp only [upLabel,triangleLabel_value,extend]
    split_ifs <;> simp [phaseZero,upAt_orientation]
  · unfold downLabel extend triangleLabel
    split_ifs <;> simp [phaseZero,downAt_orientation,PhaseLocal.flip,PhaseLocal.value]

theorem phase_one_labels (S : Support) (r : Triangles S → Bit) (e : Contacts S) :
    upLabel S (phaseOne S r) e = PhaseLocal.value (PhaseLocal.flip (triangleLabel S r (upAt e.val))) ∧
    downLabel S (phaseOne S r) e = PhaseLocal.value (triangleLabel S r (downAt e.val)) := by
  constructor
  · unfold upLabel extend triangleLabel
    split_ifs <;> simp [phaseOne,upAt_orientation,PhaseLocal.flip,PhaseLocal.value]
  · simp only [downLabel,triangleLabel_value,extend]
    split_ifs <;> simp [phaseOne,downAt_orientation]

theorem phase_zero_boundary (S : Support) (r : Triangles S → Bit) (e : Contacts S) :
    boundaryVector S (phaseZero S r) e = PhaseLocal.zeroBoundary
      (triangleLabel S r (upAt e.val)) (triangleLabel S r (downAt e.val)) := by
  have hb : boundaryVector S (phaseZero S r) e =
      upLabel S (phaseZero S r) e + downLabel S (phaseZero S r) e := by
    simp [boundaryVector,boundary_edgeValue,triangleValue_decode,upLabel,downLabel]
  rw [hb,(phase_zero_labels S r e).1,(phase_zero_labels S r e).2]
  rfl

theorem phase_one_boundary (S : Support) (r : Triangles S → Bit) (e : Contacts S) :
    boundaryVector S (phaseOne S r) e = PhaseLocal.oneBoundary
      (triangleLabel S r (upAt e.val)) (triangleLabel S r (downAt e.val)) := by
  have hb : boundaryVector S (phaseOne S r) e =
      upLabel S (phaseOne S r) e + downLabel S (phaseOne S r) e := by
    simp [boundaryVector,boundary_edgeValue,triangleValue_decode,upLabel,downLabel]
  rw [hb,(phase_one_labels S r e).1,(phase_one_labels S r e).2]
  rfl

theorem phaseSum_perimeter (S : Support) (r : Triangles S → Bit) :
    phaseSum S r PhaseLocal.perimeter = (perimeterCount S : ℤ) := by
  unfold phaseSum perimeterCount
  push_cast
  apply Finset.sum_congr rfl
  intro e _
  unfold PhaseLocal.perimeter triangleLabel triangleDegree
  split_ifs <;> simp_all

theorem phaseSum_bare (S : Support) (r : Triangles S → Bit) :
    phaseSum S r PhaseLocal.bare = (bareCount S : ℤ) := by
  unfold phaseSum bareCount
  push_cast
  apply Finset.sum_congr rfl
  intro e _
  unfold PhaseLocal.bare triangleLabel triangleDegree
  split_ifs <;> simp_all

theorem phase_omissions (S : Support) (r : Triangles S → Bit) :
    (omittedCount S (boundaryVector S r) : ℤ) = (bareCount S : ℤ) +
      phaseSum S r PhaseLocal.r + phaseSum S r PhaseLocal.a + phaseSum S r PhaseLocal.w := by
  rw [← phaseSum_bare S r]
  unfold omittedCount phaseSum
  push_cast
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [phase_boundary_labels]
  exact (PhaseLocal.table _ _).1

theorem phase_zero_up (S : Support) (r : Triangles S → Bit) :
    directedUp S (phaseZero S r) = phaseSum S r PhaseLocal.x + phaseSum S r PhaseLocal.a := by
  unfold directedUp phaseSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [(phase_zero_labels S r e).1,(phase_zero_labels S r e).2]
  exact (PhaseLocal.table _ _).2.1

theorem phase_zero_down (S : Support) (r : Triangles S → Bit) :
    directedDown S (phaseZero S r) = phaseSum S r PhaseLocal.y + phaseSum S r PhaseLocal.w := by
  unfold directedDown phaseSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [(phase_zero_labels S r e).1,(phase_zero_labels S r e).2]
  exact (PhaseLocal.table _ _).2.2.1

theorem phase_one_down (S : Support) (r : Triangles S → Bit) :
    directedDown S (phaseOne S r) = (perimeterCount S : ℤ) - phaseSum S r PhaseLocal.r -
      phaseSum S r PhaseLocal.x + phaseSum S r PhaseLocal.a := by
  rw [← phaseSum_perimeter S r]
  unfold directedDown phaseSum
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [(phase_one_labels S r e).1,(phase_one_labels S r e).2]
  exact (PhaseLocal.table _ _).2.2.2.1

theorem phase_one_up (S : Support) (r : Triangles S → Bit) :
    directedUp S (phaseOne S r) = phaseSum S r PhaseLocal.r -
      phaseSum S r PhaseLocal.y + phaseSum S r PhaseLocal.w := by
  unfold directedUp phaseSum
  rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [(phase_one_labels S r e).1,(phase_one_labels S r e).2]
  exact (PhaseLocal.table _ _).2.2.2.2.1

theorem phase_zero_gained (S : Support) (r : Triangles S → Bit) :
    (newlySelected S (boundaryVector S r) (boundaryVector S (phaseZero S r)) : ℤ) =
      phaseSum S r PhaseLocal.a + phaseSum S r PhaseLocal.w + phaseSum S r PhaseLocal.y := by
  unfold newlySelected phaseSum
  push_cast
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [phase_zero_boundary,phase_boundary_labels]
  exact (PhaseLocal.table _ _).2.2.2.2.2.1

theorem phase_zero_lost (S : Support) (r : Triangles S → Bit) :
    (newlyOmitted S (boundaryVector S r) (boundaryVector S (phaseZero S r)) : ℤ) =
      phaseSum S r PhaseLocal.x := by
  unfold newlyOmitted phaseSum
  push_cast
  apply Finset.sum_congr rfl
  intro e _
  rw [phase_zero_boundary,phase_boundary_labels]
  exact (PhaseLocal.table _ _).2.2.2.2.2.2.1

theorem phase_one_gained (S : Support) (r : Triangles S → Bit) :
    (newlySelected S (boundaryVector S r) (boundaryVector S (phaseOne S r)) : ℤ) =
      phaseSum S r PhaseLocal.a + phaseSum S r PhaseLocal.w +
      phaseSum S r PhaseLocal.r - phaseSum S r PhaseLocal.y := by
  unfold newlySelected phaseSum
  push_cast
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [phase_one_boundary,phase_boundary_labels]
  exact (PhaseLocal.table _ _).2.2.2.2.2.2.2.1

theorem phase_one_lost (S : Support) (r : Triangles S → Bit) :
    (newlyOmitted S (boundaryVector S r) (boundaryVector S (phaseOne S r)) : ℤ) =
      (perimeterCount S : ℤ) - phaseSum S r PhaseLocal.r - phaseSum S r PhaseLocal.x := by
  rw [← phaseSum_perimeter S r]
  unfold newlyOmitted phaseSum
  push_cast
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [phase_one_boundary,phase_boundary_labels]
  exact (PhaseLocal.table _ _).2.2.2.2.2.2.2.2.1

theorem phase_allocations (S : Support) (r : Triangles S → Bit) :
    phaseSum S r PhaseLocal.x ≤ (perimeterCount S : ℤ) - phaseSum S r PhaseLocal.r ∧
    phaseSum S r PhaseLocal.y ≤ phaseSum S r PhaseLocal.r := by
  rw [← phaseSum_perimeter S r,← phaseSum_sub]
  constructor
  · exact Finset.sum_le_sum (fun _ _ => (PhaseLocal.table _ _).2.2.2.2.2.2.2.2.2.1)
  · exact Finset.sum_le_sum (fun _ _ => (PhaseLocal.table _ _).2.2.2.2.2.2.2.2.2.2)

theorem phase_toggle_zero (S : Support) (r : Triangles S → Bit)
    (hm : IsMaximum S (boundaryVector S r)) :
    phaseSum S r PhaseLocal.a + phaseSum S r PhaseLocal.w ≤
      phaseSum S r PhaseLocal.x - phaseSum S r PhaseLocal.y := by
  have h := maximum_boundary_toggle S (boundaryVector S r) hm (phaseZero S r)
  have h' : (newlySelected S (boundaryVector S r) (boundaryVector S (phaseZero S r)) : ℤ) ≤
      (newlyOmitted S (boundaryVector S r) (boundaryVector S (phaseZero S r)) : ℤ) := by
    exact_mod_cast h
  rw [phase_zero_gained,phase_zero_lost] at h'
  omega

theorem phase_toggle_one (S : Support) (r : Triangles S → Bit)
    (hm : IsMaximum S (boundaryVector S r)) :
    phaseSum S r PhaseLocal.a + phaseSum S r PhaseLocal.w ≤ (perimeterCount S : ℤ) -
      2*phaseSum S r PhaseLocal.r - phaseSum S r PhaseLocal.x + phaseSum S r PhaseLocal.y := by
  have h := maximum_boundary_toggle S (boundaryVector S r) hm (phaseOne S r)
  have h' : (newlySelected S (boundaryVector S r) (boundaryVector S (phaseOne S r)) : ℤ) ≤
      (newlyOmitted S (boundaryVector S r) (boundaryVector S (phaseOne S r)) : ℤ) := by
    exact_mod_cast h
  rw [phase_one_gained,phase_one_lost] at h'
  omega

/-- Every field, including toggles and congruences, is proved from this filling. -/
def constructedPhases (S : Support) (r : Triangles S → Bit)
    (hm : IsMaximum S (boundaryVector S r)) : Tantrix.PhaseCounts where
  P := perimeterCount S
  k := phaseSum S r PhaseLocal.r + phaseSum S r PhaseLocal.a + phaseSum S r PhaseLocal.w
  r := phaseSum S r PhaseLocal.r
  a := phaseSum S r PhaseLocal.a
  w := phaseSum S r PhaseLocal.w
  x := phaseSum S r PhaseLocal.x
  y := phaseSum S r PhaseLocal.y
  P_nonneg := Int.natCast_nonneg _
  r_nonneg := phaseSum_nonneg S r _ (by intros; unfold PhaseLocal.r; split_ifs <;> omega)
  a_nonneg := phaseSum_nonneg S r _ (by intros; unfold PhaseLocal.a; split_ifs <;> omega)
  w_nonneg := phaseSum_nonneg S r _ (by intros; unfold PhaseLocal.w; split_ifs <;> omega)
  x_nonneg := phaseSum_nonneg S r _ (by intros; unfold PhaseLocal.x; split_ifs <;> omega)
  y_nonneg := phaseSum_nonneg S r _ (by intros; unfold PhaseLocal.y; split_ifs <;> omega)
  x_le := (phase_allocations S r).1
  y_le := (phase_allocations S r).2
  omissions := rfl
  toggle_zero := phase_toggle_zero S r hm
  toggle_one := phase_toggle_one S r hm
  divisible_zero := by
    have h := region_orientation_mod S (phaseZero S r)
    rwa [phase_zero_up,phase_zero_down] at h
  divisible_one := by
    have h := region_orientation_mod S (phaseOne S r)
    rw [phase_one_up,phase_one_down] at h
    omega

theorem constructedPhases_matches (S : Support) (r : Triangles S → Bit)
    (hm : IsMaximum S (boundaryVector S r)) :
    (constructedPhases S r hm).P = (perimeterCount S : ℤ) ∧
    (constructedPhases S r hm).k + (bareCount S : ℤ) =
      (omittedCount S (boundaryVector S r) : ℤ) := by
  constructor
  · rfl
  · have h := phase_omissions S r
    dsimp only [constructedPhases]
    omega

theorem phase_area_partition (S : Support) (r : Triangles S → Bit) :
    regionArea S (phaseZero S r) + regionArea S (phaseOne S r) = (triangleCount S : ℤ) := by
  rw [regionArea_sum,regionArea_sum,← Finset.sum_add_distrib]
  have ht (t : Triangles S) : bitMark (phaseZero S r t) + bitMark (phaseOne S r t) = 1 := by
    simp only [phaseZero,phaseOne]
    cases t.val.1 <;> generalize r t = z <;> fin_cases z <;> decide
  simp_rw [ht]
  simp [triangleCount]

theorem constructedPhases_area (S : Support) (r : Triangles S → Bit)
    (hm : IsMaximum S (boundaryVector S r)) (ha : DirectedAreaBound S) :
    let C := constructedPhases S r hm
    9 * (triangleCount S : ℤ) ≤
      Tantrix.areaNumerator (C.x+C.a) (C.y+C.w) +
      Tantrix.areaNumerator (C.P-C.r-C.x+C.a) (C.r-C.y+C.w) := by
  have h0 := ha (phaseZero S r)
  have h1 := ha (phaseOne S r)
  rw [phase_zero_up,phase_zero_down] at h0
  rw [phase_one_up,phase_one_down] at h1
  have hs := phase_area_partition S r
  have hsym (p q : ℤ) : Tantrix.areaNumerator p q = Tantrix.areaNumerator q p := by
    unfold Tantrix.areaNumerator; ring
  rw [hsym] at h1
  dsimp only [constructedPhases]
  omega

/-- Express an even network as the boundary of an indexed filling, using
`support_filling` to keep every filled triangle inside the support. -/
theorem exists_boundaryVector (S : Support) (hn : NoHoles S) (x : Contacts S → Bit)
    (he : (decodeEdges S x).Even) : ∃ r : Triangles S → Bit, boundaryVector S r = x := by
  obtain ⟨R,⟨_,hb,hc⟩,_⟩ := support_filling (decodeEdges S x) S he (decode_supported S x) hn
  refine ⟨fun t => triangleValue R t.val,?_⟩
  funext e
  unfold boundaryVector
  rw [decode_filling_inverse S R hc,hb,edgeValue_decode,extend_at]

/-- A maximum network supplies phase counts and the two-region area estimate.
The last implication takes `DirectedAreaBound S` as input. DirectionOrder.lean
proves it as `directed_area_bound`; GeometryApplication.lean combines the results. -/
theorem exists_phase_data (S : Support) (hn : NoHoles S) (x : Contacts S → Bit)
    (hm : IsMaximum S x) : ∃ C : Tantrix.PhaseCounts,
    C.P = (perimeterCount S : ℤ) ∧
    C.k + (bareCount S : ℤ) = (omittedCount S x : ℤ) ∧
    (DirectedAreaBound S → 9 * (triangleCount S : ℤ) ≤
      Tantrix.areaNumerator (C.x+C.a) (C.y+C.w) +
      Tantrix.areaNumerator (C.P-C.r-C.x+C.a) (C.r-C.y+C.w)) := by
  obtain ⟨r,hr⟩ := exists_boundaryVector S hn x hm.1
  subst x
  exact ⟨constructedPhases S r hm,(constructedPhases_matches S r hm).1,
    (constructedPhases_matches S r hm).2,constructedPhases_area S r hm⟩

end Tantrix.Grid
