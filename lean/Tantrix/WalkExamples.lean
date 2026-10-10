import Tantrix.BoundaryWalks
import Tantrix.AreaExamples

set_option autoImplicit false

namespace Tantrix.Grid

/-- The assembly interface covers the empty region without an exception. -/
theorem empty_boundary_word (S : Support) :
    ∃ w : List (Fin 6),
      Tantrix.Area.displacement (w.map Tantrix.Area.direction) = 0 ∧
      Tantrix.Area.wordArea (w.map Tantrix.Area.direction) = 0 ∧
      Tantrix.Area.upSteps w = 0 ∧ Tantrix.Area.downSteps w = 0 := by
  obtain ⟨w,hc,ha,hp,hq⟩ := region_boundary_word S (fun _ => 0)
  rcases empty_region_counts S with ⟨hA,hP,hQ⟩
  exact ⟨w,hc,ha.trans hA,hp.trans hP,hq.trans hQ⟩

/-- A genuine elementary triangle retains area one and directed counts (3,0). -/
theorem unitTriangle_boundary_word :
    ∃ w : List (Fin 6),
      Tantrix.Area.displacement (w.map Tantrix.Area.direction) = 0 ∧
      Tantrix.Area.wordArea (w.map Tantrix.Area.direction) = 1 ∧
      Tantrix.Area.upSteps w = 3 ∧ Tantrix.Area.downSteps w = 0 := by
  obtain ⟨w,hc,ha,hp,hq⟩ := region_boundary_word unitTriangleSupport (fun _ => 1)
  rcases unitTriangle_directed_counts with ⟨hA,hP,hQ⟩
  exact ⟨w,hc,ha.trans hA,hp.trans hP,hq.trans hQ⟩

end Tantrix.Grid

namespace Tantrix.Area

/-- A clockwise component subtracts area: a side-four outer triangle and
a unit clockwise triangle have total signed area 16 - 1 = 15. This checks
the word arithmetic used for holes; it does not classify region topology. -/
theorem signed_hole_word_example :
    let outer : List (Fin 6) := [0,0,0,0,2,2,2,2,4,4,4,4]
    let inner : List (Fin 6) := [1,5,3]
    displacement (outer.map direction) = 0 ∧
    displacement (inner.map direction) = 0 ∧
    wordArea (outer.map direction) = 16 ∧
    wordArea (inner.map direction) = -1 ∧
    wordArea ((outer ++ inner).map direction) = 15 ∧
    upSteps (outer ++ inner) = 12 ∧ downSteps (outer ++ inner) = 3 := by decide

end Tantrix.Area

namespace Tantrix.ClosedWalks

private def pairSource (e : Bool) : Fin 2 := if e then 1 else 0
private def pairTarget (e : Bool) : Fin 2 := if e then 0 else 1

/-- The general result keeps repeated edge occurrences with multiplicity. -/
theorem repeated_edges_example :
    ∃ cs : List (Walk pairSource pairTarget), (∀ c ∈ cs, c.Closed) ∧
      (cs.flatMap Walk.edges).Perm [false,true,false,true] := by
  apply decompose_edges
  intro p
  fin_cases p <;> decide

/-- Negative control: a single open edge fails the balance premise. -/
theorem open_edge_not_balanced : ¬ EdgeBalanced pairSource pairTarget [false] := by
  intro h
  have h0 := h 0
  norm_num [pairSource,pairTarget] at h0

end Tantrix.ClosedWalks
