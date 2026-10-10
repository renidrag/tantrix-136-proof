import Tantrix.Boundary
import Tantrix.Algebra

/-!
# Directed counts of finite triangle regions

A region is any bit labelling of the occupied triangles. No connectedness,
convexity or absence of holes is assumed for a region.
-/

set_option autoImplicit false
open scoped BigOperators
open Classical
noncomputable section

namespace Tantrix.Grid

def bitMark (z : Bit) : ℤ := if z = 0 then 0 else 1

theorem bitMark_nonneg (z : Bit) : 0 ≤ bitMark z := by unfold bitMark; split_ifs <;> omega

theorem extend_mark_sum {I : Type*} [DecidableEq I] {P : I → Prop}
    [Fintype {i // P i}] (r : {i // P i} → Bit) (i : I) :
    bitMark (extend r i) = ∑ t, if t.val = i then bitMark (r t) else 0 := by
  by_cases hi : P i
  · rw [Finset.sum_eq_single (⟨i,hi⟩ : {i // P i})]
    · simp [extend,hi]
    · intro t _ ht
      have hti : t.val ≠ i := fun h => ht (Subtype.ext h)
      simp [hti]
    · simp
  · have ht : ∀ t : {i // P i}, t.val ≠ i := fun t h => hi (h ▸ t.property)
    simp [extend,hi,ht,bitMark]

def regionUp (S : Support) (r : Triangles S → Bit) : ℤ :=
  ∑ t, if t.val.1 then 0 else bitMark (r t)
def regionDown (S : Support) (r : Triangles S → Bit) : ℤ :=
  ∑ t, if t.val.1 then bitMark (r t) else 0
def regionArea (S : Support) (r : Triangles S → Bit) : ℤ := regionUp S r + regionDown S r

def upLabel (S : Support) (r : Triangles S → Bit) (e : Contacts S) : Bit := extend r (upAt e.val)
def downLabel (S : Support) (r : Triangles S → Bit) (e : Contacts S) : Bit := extend r (downAt e.val)

def directedUp (S : Support) (r : Triangles S → Bit) : ℤ :=
  ∑ e, if upLabel S r e ≠ 0 ∧ downLabel S r e = 0 then 1 else 0
def directedDown (S : Support) (r : Triangles S → Bit) : ℤ :=
  ∑ e, if downLabel S r e ≠ 0 ∧ upLabel S r e = 0 then 1 else 0
def regionInternal (S : Support) (r : Triangles S → Bit) : ℤ :=
  ∑ e, if upLabel S r e ≠ 0 ∧ downLabel S r e ≠ 0 then 1 else 0

theorem triangle_sides_count (S : Support) (t : Triangles S) :
    (∑ e : Contacts S, ((if t.val = upAt e.val then (1 : ℤ) else 0) +
      (if t.val = downAt e.val then 1 else 0))) = 3 := by
  have hi (e : Contacts S) := triangleSide_incidence t.val e.val
  have hi' (e : Contacts S) :
      (if t.val = upAt e.val then (1 : ℤ) else 0) +
      (if t.val = downAt e.val then 1 else 0) =
      ∑ k : Fin 3, if triangleSide t.val k = e.val then 1 else 0 := by
    exact_mod_cast (hi e).symm
  simp_rw [hi']
  rw [Finset.sum_comm]
  have hs (k : Fin 3) :
      (∑ e : Contacts S, if triangleSide t.val k = e.val then (1 : ℤ) else 0) = 1 := by
    have h := present_sum (P := edgePresent S) (triangleSide t.val k)
    have h' : (∑ e : Contacts S, if triangleSide t.val k = e.val then (1 : ℕ) else 0) = 1 := by
      simpa only [triangleSide_present S t k,ite_true,eq_comm] using h.symm
    exact_mod_cast h'
  simp_rw [hs]
  simp

theorem upAt_orientation (e : EdgeIndex) : (upAt e).1 = false := rfl
theorem downAt_orientation (e : EdgeIndex) : (downAt e).1 = true := by
  unfold downAt; split_ifs <;> rfl

theorem triangle_up_sides (S : Support) (t : Triangles S) :
    (∑ e : Contacts S, if t.val = upAt e.val then (1 : ℤ) else 0) =
      if t.val.1 then 0 else 3 := by
  have h := triangle_sides_count S t
  rw [Finset.sum_add_distrib] at h
  cases ht : t.val.1
  · have hn (e : Contacts S) : t.val ≠ downAt e.val := by
      intro he; have := congrArg Prod.fst he
      rw [ht,downAt_orientation] at this; contradiction
    simp only [hn,ite_false,Finset.sum_const_zero,add_zero] at h
    simpa [ht] using h
  · have hn (e : Contacts S) : t.val ≠ upAt e.val := by
      intro he; have := congrArg Prod.fst he
      rw [ht,upAt_orientation] at this; contradiction
    simp [hn]

theorem triangle_down_sides (S : Support) (t : Triangles S) :
    (∑ e : Contacts S, if t.val = downAt e.val then (1 : ℤ) else 0) =
      if t.val.1 then 3 else 0 := by
  have h := triangle_sides_count S t
  rw [Finset.sum_add_distrib,triangle_up_sides] at h
  cases ht : t.val.1 <;> simp_all

theorem region_up_incidence (S : Support) (r : Triangles S → Bit) :
    (∑ e, bitMark (upLabel S r e)) = 3 * regionUp S r := by
  simp only [upLabel,extend_mark_sum]
  rw [Finset.sum_comm]
  unfold regionUp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  have h : (∑ e : Contacts S, if t.val = upAt e.val then bitMark (r t) else 0) =
      (∑ e : Contacts S, if t.val = upAt e.val then (1 : ℤ) else 0) * bitMark (r t) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _; split_ifs <;> simp
  rw [h,triangle_up_sides]
  cases t.val.1 <;> simp

theorem region_down_incidence (S : Support) (r : Triangles S → Bit) :
    (∑ e, bitMark (downLabel S r e)) = 3 * regionDown S r := by
  simp only [downLabel,extend_mark_sum]
  rw [Finset.sum_comm]
  unfold regionDown
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  have h : (∑ e : Contacts S, if t.val = downAt e.val then bitMark (r t) else 0) =
      (∑ e : Contacts S, if t.val = downAt e.val then (1 : ℤ) else 0) * bitMark (r t) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _; split_ifs <;> simp
  rw [h,triangle_down_sides]
  cases t.val.1 <;> simp

theorem region_up_count (S : Support) (r : Triangles S → Bit) :
    3 * regionUp S r = regionInternal S r + directedUp S r := by
  rw [← region_up_incidence]
  unfold regionInternal directedUp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  unfold bitMark
  by_cases hu : upLabel S r e = 0 <;> by_cases hd : downLabel S r e = 0 <;> simp [hu,hd]

theorem region_down_count (S : Support) (r : Triangles S → Bit) :
    3 * regionDown S r = regionInternal S r + directedDown S r := by
  rw [← region_down_incidence]
  unfold regionInternal directedDown
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  unfold bitMark
  by_cases hu : upLabel S r e = 0 <;> by_cases hd : downLabel S r e = 0 <;> simp [hu,hd]

theorem region_orientation_count (S : Support) (r : Triangles S → Bit) :
    directedUp S r - directedDown S r = 3 * (regionUp S r - regionDown S r) := by
  have hu := region_up_count S r
  have hd := region_down_count S r
  omega

theorem region_orientation_mod (S : Support) (r : Triangles S → Bit) :
    (directedUp S r - directedDown S r) % 3 = 0 := by
  rw [region_orientation_count]; omega

theorem region_boundary_count (S : Support) (r : Triangles S → Bit) :
    directedUp S r + directedDown S r = (selectedCount S (boundaryVector S r) : ℤ) := by
  unfold directedUp directedDown selectedCount
  push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hb : boundaryVector S r e = upLabel S r e + downLabel S r e := by
    simp [boundaryVector,boundary_edgeValue,triangleValue_decode,upLabel,downLabel]
  rw [hb]
  generalize upLabel S r e = a, downLabel S r e = b
  fin_cases a <;> fin_cases b <;> decide

theorem regionArea_sum (S : Support) (r : Triangles S → Bit) :
    regionArea S r = ∑ t, bitMark (r t) := by
  unfold regionArea regionUp regionDown
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _; cases t.val.1 <;> simp

theorem whole_regionArea (S : Support) : regionArea S (fun _ => 1) = triangleCount S := by
  simp [regionArea_sum,bitMark,triangleCount]

theorem directedUp_nonneg (S : Support) (r : Triangles S → Bit) : 0 ≤ directedUp S r := by
  apply Finset.sum_nonneg
  intro e _; split_ifs <;> omega

theorem directedDown_nonneg (S : Support) (r : Triangles S → Bit) : 0 ≤ directedDown S r := by
  apply Finset.sum_nonneg
  intro e _; split_ifs <;> omega

/-- The directed area inequality for every region of occupied triangles.
`Tantrix.Grid.directed_area_bound` in DirectionOrder.lean proves this property
for every support, using the region boundary construction and word rearrangement. -/
def DirectedAreaBound (S : Support) : Prop :=
  ∀ r : Triangles S → Bit, 9 * regionArea S r ≤ Tantrix.areaNumerator (directedUp S r) (directedDown S r)

end Tantrix.Grid
