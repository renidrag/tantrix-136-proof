import Tantrix.AreaBoundary

/-!
# Oriented boundary contacts

Only contacts whose two triangle labels differ are included. Orientation
keeps the selected triangle on the left. Each contact is indexed once.
-/

set_option autoImplicit false
open scoped BigOperators
open Classical
noncomputable section

namespace Tantrix.Grid

namespace BoundaryOrientation

def forward (e : EdgeIndex) (up : Bit) : Prop :=
  if e.1 = 1 then up = 0 else up ≠ 0
def source (e : EdgeIndex) (up : Bit) : Vertex :=
  if forward e up then edgeFirst e else edgeLast e
def target (e : EdgeIndex) (up : Bit) : Vertex :=
  if forward e up then edgeLast e else edgeFirst e
def direction (e : EdgeIndex) (up : Bit) : Fin 6 :=
  if up = 0 then ![3,1,5] e.1 else ![0,4,2] e.1

theorem bit_cases (a : Bit) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem different_bits (a b : Bit) (h : a ≠ b) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;> simp_all

theorem step_eq_direction (e : EdgeIndex) (up : Bit) :
    target e up - source e up = Tantrix.Area.direction (direction e up) := by
  rcases e with ⟨d,i,j⟩
  rcases bit_cases up with rfl | rfl <;> fin_cases d <;>
    ext <;> simp [source,target,forward,direction,Tantrix.Area.direction,edgeFirst,edgeLast]

theorem flux (e : EdgeIndex) (up down : Bit) (hd : up ≠ down) (p : Vertex) :
    ((if target e up = p then (1 : ℤ) else 0) - (if source e up = p then 1 else 0)) =
      (bitMark up - bitMark down) * (edgeSign e *
        ((if edgeLast e = p then (1 : ℤ) else 0) - (if edgeFirst e = p then 1 else 0))) := by
  rcases different_bits up down hd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    by_cases hv : e.1 = 1 <;> by_cases hf : edgeFirst e = p <;>
    by_cases hl : edgeLast e = p <;>
    simp [source,target,forward,bitMark,edgeSign,hv,hf,hl]

theorem area (e : EdgeIndex) (up down : Bit) (hd : up ≠ down) :
    Tantrix.Area.det (source e up) (target e up) =
      (bitMark up - bitMark down) *
        (edgeSign e * Tantrix.Area.det (edgeFirst e) (edgeLast e)) := by
  rcases different_bits up down hd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    by_cases hv : e.1 = 1 <;>
    simp [source,target,forward,bitMark,edgeSign,hv,Tantrix.Area.det] <;> ring

theorem even_direction (e : EdgeIndex) (up down : Bit) (hd : up ≠ down) :
    (if (direction e up).val % 2 = 0 then (1 : ℤ) else 0) =
      if up ≠ 0 ∧ down = 0 then 1 else 0 := by
  rcases e with ⟨d,i,j⟩
  rcases different_bits up down hd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    fin_cases d <;> norm_num [direction]

theorem odd_direction (e : EdgeIndex) (up down : Bit) (hd : up ≠ down) :
    (if (direction e up).val % 2 = 1 then (1 : ℤ) else 0) =
      if down ≠ 0 ∧ up = 0 then 1 else 0 := by
  rcases e with ⟨d,i,j⟩
  rcases different_bits up down hd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    fin_cases d <;> norm_num [direction]

end BoundaryOrientation

def boundaryActive (S : Support) (r : Triangles S → Bit) (e : Contacts S) : Prop :=
  upLabel S r e ≠ downLabel S r e

abbrev BoundaryEdges (S : Support) (r : Triangles S → Bit) := {e : Contacts S // boundaryActive S r e}

instance boundaryEdgesFintype (S : Support) (r : Triangles S → Bit) : Fintype (BoundaryEdges S r) :=
  Subtype.fintype _

def boundarySource (S : Support) (r : Triangles S → Bit) (e : BoundaryEdges S r) : Vertex :=
  BoundaryOrientation.source e.val.val (upLabel S r e.val)
def boundaryTarget (S : Support) (r : Triangles S → Bit) (e : BoundaryEdges S r) : Vertex :=
  BoundaryOrientation.target e.val.val (upLabel S r e.val)
def boundaryDirection (S : Support) (r : Triangles S → Bit) (e : BoundaryEdges S r) : Fin 6 :=
  BoundaryOrientation.direction e.val.val (upLabel S r e.val)

def boundaryEnumeration (S : Support) (r : Triangles S → Bit) : List (BoundaryEdges S r) :=
  Finset.univ.toList

theorem boundary_step (S : Support) (r : Triangles S → Bit) (e : BoundaryEdges S r) :
    boundaryTarget S r e - boundarySource S r e = Tantrix.Area.direction (boundaryDirection S r e) :=
  BoundaryOrientation.step_eq_direction _ _

theorem boundary_sum_of_zero (S : Support) (r : Triangles S → Bit) (f : Contacts S → ℤ)
    (hf : ∀ e, ¬ boundaryActive S r e → f e = 0) :
    (∑ e : BoundaryEdges S r, f e.val) = ∑ e : Contacts S, f e := by
  rw [← Finset.sum_subtype (Finset.univ.filter (boundaryActive S r)) (by simp) f,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : boundaryActive S r e
  · simp [he]
  · simp [he,hf e he]

theorem boundary_flux_sum (S : Support) (r : Triangles S → Bit) (p : Vertex) :
    (∑ e : BoundaryEdges S r,
      ((if boundaryTarget S r e = p then (1 : ℤ) else 0) -
       (if boundarySource S r e = p then 1 else 0))) = 0 := by
  have he (e : BoundaryEdges S r) :=
    BoundaryOrientation.flux e.val.val (upLabel S r e.val) (downLabel S r e.val) e.property p
  simp_rw [show ∀ e : BoundaryEdges S r,
      ((if boundaryTarget S r e = p then (1 : ℤ) else 0) -
       (if boundarySource S r e = p then 1 else 0)) =
      (bitMark (upLabel S r e.val) - bitMark (downLabel S r e.val)) *
        (edgeSign e.val.val * ((if edgeLast e.val.val = p then (1 : ℤ) else 0) -
          (if edgeFirst e.val.val = p then 1 else 0))) from he]
  rw [boundary_sum_of_zero S r (fun e =>
      (bitMark (upLabel S r e) - bitMark (downLabel S r e)) *
        (edgeSign e.val * ((if edgeLast e.val = p then (1 : ℤ) else 0) -
          (if edgeFirst e.val = p then 1 else 0)))) (by
    intro e h
    have hz : upLabel S r e = downLabel S r e := by simpa [boundaryActive] using h
    simp [hz])]
  exact region_boundary_balanced S r p

theorem boundary_area_sum (S : Support) (r : Triangles S → Bit) :
    (∑ e : BoundaryEdges S r, Tantrix.Area.det (boundarySource S r e) (boundaryTarget S r e)) =
      regionArea S r := by
  have he (e : BoundaryEdges S r) :
      Tantrix.Area.det (boundarySource S r e) (boundaryTarget S r e) =
        (bitMark (upLabel S r e.val) - bitMark (downLabel S r e.val)) *
          (edgeSign e.val.val * Tantrix.Area.det (edgeFirst e.val.val) (edgeLast e.val.val)) :=
    BoundaryOrientation.area _ _ _ e.property
  simp_rw [he]
  rw [boundary_sum_of_zero S r (fun e =>
      (bitMark (upLabel S r e) - bitMark (downLabel S r e)) *
        (edgeSign e.val * Tantrix.Area.det (edgeFirst e.val) (edgeLast e.val))) (by
    intro e h
    have hz : upLabel S r e = downLabel S r e := by simpa [boundaryActive] using h
    simp [hz])]
  exact region_boundary_area S r

theorem boundary_even_sum (S : Support) (r : Triangles S → Bit) :
    (∑ e : BoundaryEdges S r, if (boundaryDirection S r e).val % 2 = 0 then (1 : ℤ) else 0) =
      directedUp S r := by
  have he (e : BoundaryEdges S r) :
      (if (boundaryDirection S r e).val % 2 = 0 then (1 : ℤ) else 0) =
        if upLabel S r e.val ≠ 0 ∧ downLabel S r e.val = 0 then 1 else 0 :=
    BoundaryOrientation.even_direction _ _ _ e.property
  simp_rw [he]
  rw [boundary_sum_of_zero S r (fun e =>
      if upLabel S r e ≠ 0 ∧ downLabel S r e = 0 then (1 : ℤ) else 0) (by
    intro e h
    have hz : upLabel S r e = downLabel S r e := by simpa [boundaryActive] using h
    simp [hz])]
  rfl

theorem boundary_odd_sum (S : Support) (r : Triangles S → Bit) :
    (∑ e : BoundaryEdges S r, if (boundaryDirection S r e).val % 2 = 1 then (1 : ℤ) else 0) =
      directedDown S r := by
  have he (e : BoundaryEdges S r) :
      (if (boundaryDirection S r e).val % 2 = 1 then (1 : ℤ) else 0) =
        if downLabel S r e.val ≠ 0 ∧ upLabel S r e.val = 0 then 1 else 0 :=
    BoundaryOrientation.odd_direction _ _ _ e.property
  simp_rw [he]
  rw [boundary_sum_of_zero S r (fun e =>
      if downLabel S r e ≠ 0 ∧ upLabel S r e = 0 then (1 : ℤ) else 0) (by
    intro e h
    have hz : upLabel S r e = downLabel S r e := by simpa [boundaryActive] using h
    simp [hz])]
  rfl

end Tantrix.Grid
