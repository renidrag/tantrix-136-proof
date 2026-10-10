import Tantrix.Counting

set_option autoImplicit false
open scoped BigOperators
open Classical
noncomputable section

namespace Tantrix.Grid

def boundaryVector (S : Support) (r : Triangles S → Bit) : Contacts S → Bit :=
  fun e => edgeValue (decodeFilling S r).boundary e.val

theorem boundaryVector_even (S : Support) (r : Triangles S → Bit) :
    (decodeEdges S (boundaryVector S r)).Even := by
  unfold boundaryVector
  rw [decode_edges_inverse S _
    (boundary_supported _ S (decode_contained S r))]
  exact boundary_even _

theorem even_add (S : Support) (x y : Contacts S → Bit)
    (hx : (decodeEdges S x).Even) (hy : (decodeEdges S y).Even) :
    (decodeEdges S (x+y)).Even := by
  apply (decode_even_iff S _).mpr
  change (incidence S).transpose.mulVecLin (x+y) = 0
  rw [map_add]
  change (incidence S).transpose.mulVec x + (incidence S).transpose.mulVec y = 0
  rw [(decode_even_iff S x).mp hx,(decode_even_iff S y).mp hy,add_zero]

def IsMaximum (S : Support) (x : Contacts S → Bit) : Prop :=
  (decodeEdges S x).Even ∧ ∀ y : Contacts S → Bit,
    (decodeEdges S y).Even → selectedCount S y ≤ selectedCount S x

theorem exists_maximum (S : Support) : ∃ x, IsMaximum S x := by
  have hz : (decodeEdges S (0 : Contacts S → Bit)).Even := by
    apply (decode_even_iff S _).mpr
    exact (incidence S).transpose.mulVecLin.map_zero
  let candidates := Finset.univ.filter (fun x : Contacts S → Bit => (decodeEdges S x).Even)
  have hne : candidates.Nonempty := ⟨0, by simp [candidates,hz]⟩
  obtain ⟨x,hx,hm⟩ := Finset.exists_max_image candidates (selectedCount S) hne
  refine ⟨x,(Finset.mem_filter.mp hx).2,?_⟩
  intro y hy
  exact hm y (by simp [candidates,hy])

def newlySelected (S : Support) (x y : Contacts S → Bit) : ℕ :=
  ∑ e, if y e ≠ 0 ∧ x e = 0 then 1 else 0
def newlyOmitted (S : Support) (x y : Contacts S → Bit) : ℕ :=
  ∑ e, if y e ≠ 0 ∧ x e ≠ 0 then 1 else 0

theorem bit_toggle_count (a b : Bit) :
    (if a+b = 0 then (0 : ℕ) else 1) + (if b ≠ 0 ∧ a ≠ 0 then 1 else 0) =
      (if a = 0 then 0 else 1) + (if b ≠ 0 ∧ a = 0 then 1 else 0) := by
  fin_cases a <;> fin_cases b <;> decide

theorem toggle_count (S : Support) (x y : Contacts S → Bit) :
    selectedCount S (x+y) + newlyOmitted S x y =
      selectedCount S x + newlySelected S x y := by
  unfold selectedCount newlyOmitted newlySelected
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun e _ => bit_toggle_count (x e) (y e))

/-- Any even toggle of a largest even network has at least as many retained
as omitted contacts. No connectedness or no-holes assumption is needed. -/
theorem maximum_toggle (S : Support) (x y : Contacts S → Bit)
    (hx : IsMaximum S x) (hy : (decodeEdges S y).Even) :
    newlySelected S x y ≤ newlyOmitted S x y := by
  have hc := toggle_count S x y
  have hm := hx.2 (x+y) (even_add S x y hx.1 hy)
  omega

theorem maximum_boundary_toggle (S : Support) (x : Contacts S → Bit)
    (hx : IsMaximum S x) (r : Triangles S → Bit) :
    newlySelected S x (boundaryVector S r) ≤ newlyOmitted S x (boundaryVector S r) :=
  maximum_toggle S x _ hx (boundaryVector_even S r)

/-- Selecting every occupied triangle leaves precisely the one-triangle
contacts on the boundary. Zero-triangle contacts are not perimeter edges. -/
theorem whole_boundary_iff (S : Support) (e : Contacts S) :
    boundaryVector S (fun _ => 1) e ≠ 0 ↔ triangleDegree S e.val = 1 := by
  unfold boundaryVector
  rw [boundary_edgeValue,triangleValue_decode,triangleValue_decode]
  unfold extend triangleDegree
  by_cases hu : trianglePresent S (upAt e.val) <;>
    by_cases hd : trianglePresent S (downAt e.val) <;> simp [hu,hd]

theorem whole_boundary_count (S : Support) :
    selectedCount S (boundaryVector S (fun _ => 1)) = perimeterCount S := by
  apply Finset.sum_congr rfl
  intro e _
  have h := whole_boundary_iff S e
  by_cases hb : boundaryVector S (fun _ => 1) e = 0
  · have hn : triangleDegree S e.val ≠ 1 := fun he => h.mpr he hb
    simp [hb,hn]
  · simp [hb,h.mp hb]

end Tantrix.Grid
