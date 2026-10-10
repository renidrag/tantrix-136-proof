import Tantrix.Regions
import Tantrix.AreaWords

/-!
# Integer boundary integrals

Summing the counterclockwise boundaries of occupied elementary triangles
cancels internal edges. This is a finite-sum identity, valid even with
holes, pinches and disconnected regions.
-/

set_option autoImplicit false
open scoped BigOperators
open Classical
noncomputable section

namespace Tantrix.Grid

/-- The up-triangle orientation agrees with the canonical edge orientation
except on vertical contacts. -/
def edgeSign (e : EdgeIndex) : ℤ := if e.1 = 1 then -1 else 1
def triangleSign (t : TriangleIndex) : ℤ := if t.1 then -1 else 1

theorem triangle_side_integral (S : Support) (t : Triangles S) (f : EdgeIndex → ℤ) :
    (∑ e : Contacts S, ((if t.val = upAt e.val then (1 : ℤ) else 0) +
      (if t.val = downAt e.val then 1 else 0)) * f e.val) =
      ∑ k : Fin 3, f (triangleSide t.val k) := by
  have hi (e : Contacts S) :
      (if t.val = upAt e.val then (1 : ℤ) else 0) +
      (if t.val = downAt e.val then 1 else 0) =
      ∑ k : Fin 3, if triangleSide t.val k = e.val then 1 else 0 := by
    exact_mod_cast (triangleSide_incidence t.val e.val).symm
  simp_rw [hi,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single (⟨triangleSide t.val k,triangleSide_present S t k⟩ : Contacts S)]
  · simp
  · intro e _ he
    have hn : triangleSide t.val k ≠ e.val := fun h => he (Subtype.ext h.symm)
    simp [hn]
  · simp

theorem oriented_triangle_integral (S : Support) (t : Triangles S) (f : EdgeIndex → ℤ) :
    (∑ e : Contacts S, ((if t.val = upAt e.val then (1 : ℤ) else 0) -
      (if t.val = downAt e.val then 1 else 0)) * f e.val) =
      triangleSign t.val * ∑ k : Fin 3, f (triangleSide t.val k) := by
  rw [← triangle_side_integral S t f,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  cases ht : t.val.1
  · have hn : t.val ≠ downAt e.val := by
      intro he; have := congrArg Prod.fst he
      rw [ht,downAt_orientation] at this; contradiction
    simp [triangleSign,ht,hn]
  · have hn : t.val ≠ upAt e.val := by
      intro he; have := congrArg Prod.fst he
      rw [ht,upAt_orientation] at this; contradiction
    simp only [triangleSign,ht,ite_true,hn,ite_false]
    split_ifs <;> ring

/-- Discrete Stokes formula for any scalar edge weight. -/
theorem region_boundary_integral (S : Support) (r : Triangles S → Bit) (f : EdgeIndex → ℤ) :
    (∑ e : Contacts S, (bitMark (upLabel S r e) - bitMark (downLabel S r e)) * f e.val) =
      ∑ t : Triangles S, bitMark (r t) * triangleSign t.val *
        ∑ k : Fin 3, f (triangleSide t.val k) := by
  simp only [upLabel,downLabel,extend_mark_sum]
  simp_rw [← Finset.sum_sub_distrib,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  have h : (∑ e : Contacts S,
      ((if t.val = upAt e.val then bitMark (r t) else 0) -
       (if t.val = downAt e.val then bitMark (r t) else 0)) * f e.val) =
      bitMark (r t) * ∑ e : Contacts S,
        ((if t.val = upAt e.val then (1 : ℤ) else 0) -
         (if t.val = downAt e.val then 1 else 0)) * f e.val := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> ring
  rw [h,oriented_triangle_integral]
  ring

theorem triangle_unit_area (t : TriangleIndex) :
    triangleSign t * (∑ k : Fin 3, edgeSign (triangleSide t k) *
      Tantrix.Area.det (edgeFirst (triangleSide t k)) (edgeLast (triangleSide t k))) = 1 := by
  rcases t with ⟨b,i,j⟩
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  cases b <;> norm_num [triangleSign,triangleSide,edgeSign,edgeFirst,edgeLast,Tantrix.Area.det] <;> ring

/-- A boundary integral is exactly the number of selected unit triangles. -/
theorem region_boundary_area (S : Support) (r : Triangles S → Bit) :
    (∑ e : Contacts S, (bitMark (upLabel S r e) - bitMark (downLabel S r e)) *
      (edgeSign e.val * Tantrix.Area.det (edgeFirst e.val) (edgeLast e.val))) = regionArea S r := by
  rw [region_boundary_integral S r (fun e => edgeSign e * Tantrix.Area.det (edgeFirst e) (edgeLast e)),regionArea_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [mul_assoc,triangle_unit_area,mul_one]

theorem triangle_closed_first (t : TriangleIndex) :
    triangleSign t * (∑ k : Fin 3, edgeSign (triangleSide t k) *
      ((edgeLast (triangleSide t k)).1 - (edgeFirst (triangleSide t k)).1)) = 0 := by
  rcases t with ⟨b,i,j⟩
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  cases b <;> simp [triangleSign,triangleSide,edgeSign,edgeFirst,edgeLast]

theorem triangle_closed_second (t : TriangleIndex) :
    triangleSign t * (∑ k : Fin 3, edgeSign (triangleSide t k) *
      ((edgeLast (triangleSide t k)).2 - (edgeFirst (triangleSide t k)).2)) = 0 := by
  rcases t with ⟨b,i,j⟩
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  cases b <;> simp [triangleSign,triangleSide,edgeSign,edgeFirst,edgeLast]

/-- The oriented region boundary has zero net displacement in both axes. -/
theorem region_boundary_closed (S : Support) (r : Triangles S → Bit) :
    (∑ e : Contacts S, (bitMark (upLabel S r e) - bitMark (downLabel S r e)) *
      (edgeSign e.val * ((edgeLast e.val).1 - (edgeFirst e.val).1))) = 0 ∧
    (∑ e : Contacts S, (bitMark (upLabel S r e) - bitMark (downLabel S r e)) *
      (edgeSign e.val * ((edgeLast e.val).2 - (edgeFirst e.val).2))) = 0 := by
  constructor
  · rw [region_boundary_integral S r (fun e => edgeSign e * ((edgeLast e).1 - (edgeFirst e).1))]
    simp only [mul_assoc,triangle_closed_first,mul_zero,Finset.sum_const_zero]
  · rw [region_boundary_integral S r (fun e => edgeSign e * ((edgeLast e).2 - (edgeFirst e).2))]
    simp only [mul_assoc,triangle_closed_second,mul_zero,Finset.sum_const_zero]

theorem triangle_boundary_balanced (t : TriangleIndex) (p : Vertex) :
    triangleSign t * (∑ k : Fin 3, edgeSign (triangleSide t k) *
      ((if edgeLast (triangleSide t k) = p then (1 : ℤ) else 0) -
       (if edgeFirst (triangleSide t k) = p then 1 else 0))) = 0 := by
  rcases t with ⟨b,i,j⟩
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  cases b <;> norm_num [triangleSign,triangleSide,edgeSign,edgeFirst,edgeLast]

/-- At every lattice vertex, the signed number of incoming and outgoing
boundary edges agrees. This includes pinches and multiple components. -/
theorem region_boundary_balanced (S : Support) (r : Triangles S → Bit) (p : Vertex) :
    (∑ e : Contacts S, (bitMark (upLabel S r e) - bitMark (downLabel S r e)) *
      (edgeSign e.val * ((if edgeLast e.val = p then (1 : ℤ) else 0) -
        (if edgeFirst e.val = p then 1 else 0)))) = 0 := by
  rw [region_boundary_integral S r (fun e => edgeSign e *
    ((if edgeLast e = p then (1 : ℤ) else 0) - (if edgeFirst e = p then 1 else 0)))]
  simp only [mul_assoc,triangle_boundary_balanced,mul_zero,Finset.sum_const_zero]

end Tantrix.Grid
