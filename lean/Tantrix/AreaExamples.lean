import Tantrix.Phases
import Tantrix.AreaWords
import Tantrix.CountingExamples

set_option autoImplicit false
open scoped BigOperators
open Classical
noncomputable section

namespace Tantrix.Grid

theorem empty_region_counts (S : Support) :
    regionArea S (fun _ => 0) = 0 ∧ directedUp S (fun _ => 0) = 0 ∧
    directedDown S (fun _ => 0) = 0 := by
  have hz (t : TriangleIndex) : extend (fun _ : Triangles S => 0) t = 0 := by
    unfold extend; split_ifs <;> rfl
  simp [regionArea_sum,bitMark,directedUp,directedDown,upLabel,downLabel,hz]

/-- The elementary up triangle has area one and directed boundary (3,0). -/
theorem unitTriangle_directed_counts :
    regionArea unitTriangleSupport (fun _ => 1) = 1 ∧
    directedUp unitTriangleSupport (fun _ => 1) = 3 ∧
    directedDown unitTriangleSupport (fun _ => 1) = 0 := by
  have hA : regionArea unitTriangleSupport (fun _ => 1) = 1 := by
    rw [whole_regionArea,unitTriangle_triangleCount]; norm_num
  have hD : regionDown unitTriangleSupport (fun _ => 1) = 0 := by
    unfold regionDown
    have h (t : Triangles unitTriangleSupport) : t.val.1 = false :=
      congrArg Prod.fst (unitTriangle_unique t)
    simp [h]
  have hu := region_up_count unitTriangleSupport (fun _ => 1)
  have hd := region_down_count unitTriangleSupport (fun _ => 1)
  have hi : 0 ≤ regionInternal unitTriangleSupport (fun _ => 1) := by
    apply Finset.sum_nonneg
    intro e _; split_ifs <;> omega
  have hq := directedDown_nonneg unitTriangleSupport (fun _ => 1)
  refine ⟨hA,?_⟩
  dsimp only [regionArea] at hA
  omega

/-- A genuine support satisfies the directed bound, checked for both of its
triangle subsets. This is a definition check, not the general area theorem. -/
theorem unitTriangle_directed_area : DirectedAreaBound unitTriangleSupport := by
  intro r
  let t : Triangles unitTriangleSupport :=
    ⟨(false,0,0),by simp [trianglePresent,triangleVertices,unitTriangleSupport]⟩
  have hr : r = fun _ => r t := by
    funext u
    have hu : u = t := Subtype.ext (unitTriangle_unique u)
    rw [hu]
  rw [hr]
  generalize r t = z
  have hz : z = 0 ∨ z = 1 := by
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hz with rfl | rfl
  · rcases empty_region_counts unitTriangleSupport with ⟨ha,hp,hq⟩
    rw [ha,hp,hq]
    norm_num [Tantrix.areaNumerator]
  · rcases unitTriangle_directed_counts with ⟨ha,hp,hq⟩
    rw [ha,hp,hq]
    norm_num [Tantrix.areaNumerator]

theorem unitTriangle_full_maximum :
    IsMaximum unitTriangleSupport (boundaryVector unitTriangleSupport (fun _ => 1)) := by
  have hscore : selectedCount unitTriangleSupport (boundaryVector unitTriangleSupport (fun _ => 1)) = 3 := by
    have h := region_boundary_count unitTriangleSupport (fun _ => 1)
    rw [unitTriangle_directed_counts.2.1,unitTriangle_directed_counts.2.2] at h
    omega
  refine ⟨boundaryVector_even _ _,?_⟩
  intro x _
  have h := selection_partition unitTriangleSupport x
  have he := unitTriangle_counts.2.1
  omega

/-- The constructed phase record exists on an actual maximum network. -/
theorem unitTriangle_phase_data : ∃ C : Tantrix.PhaseCounts, C.P = 3 ∧ C.k = 0 := by
  have hC := constructedPhases_matches unitTriangleSupport (fun _ => 1) unitTriangle_full_maximum
  have hb := region_boundary_count unitTriangleSupport (fun _ => 1)
  have hs := selection_partition unitTriangleSupport (boundaryVector unitTriangleSupport (fun _ => 1))
  have hbare := bare_le_omitted unitTriangleSupport unitTriangle_no_holes
    (boundaryVector unitTriangleSupport (fun _ => 1)) (boundaryVector_even _ _)
  have he := unitTriangle_counts.2.1
  rw [unitTriangle_directed_counts.2.1,unitTriangle_directed_counts.2.2] at hb
  have hP := whole_boundary_count unitTriangleSupport
  refine ⟨constructedPhases unitTriangleSupport (fun _ => 1) unitTriangle_full_maximum,?_,?_⟩ <;> omega

end Tantrix.Grid

namespace Tantrix.Area

/-- A unit up triangle and a six-step regular hexagon attain the directed
word inequality. These test the area normalization and direction order. -/
theorem sorted_small_examples :
    displacement (sortedWord 1 0 1 0 1 0) = 0 ∧
    wordArea (sortedWord 1 0 1 0 1 0) = 1 ∧
    displacement (sortedWord 1 1 1 1 1 1) = 0 ∧
    wordArea (sortedWord 1 1 1 1 1 1) = 6 := by decide

end Tantrix.Area
