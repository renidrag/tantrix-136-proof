import Tantrix.GeneralBounds
import Tantrix.PhysicalLoops

/-!
# Disconnected supports

Rank-nullity supplies the component correction to Euler counting. The existing
area and phase estimates need no connectedness. Adding the nonnegative counting
correction to the omission budget, and twice it to the boundary budget, restores
the connected counting identities. The already-checked bridge inequality
preserves the phase bound, so no geometric relocation or new contacts are needed.
-/

set_option autoImplicit false
open scoped BigOperators
open Classical
noncomputable section

namespace Tantrix.FiniteGraph
open Tantrix.Grid

variable {V E : Type*} [Fintype V] [DecidableEq V]

/-- Rank-nullity before specializing the vertex kernel to constants. -/
theorem cycle_dimension_general [Fintype E] (a b : E → V) :
    Module.finrank Bit (LinearMap.ker (incidence a b).transpose.mulVecLin) +
      Fintype.card V = Fintype.card E +
        Module.finrank Bit (LinearMap.ker (incidence a b).mulVecLin) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (K := Bit) (incidence a b).mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker (K := Bit) (incidence a b).transpose.mulVecLin
  rw [Module.finrank_pi] at h1 h2
  have hr := Matrix.rank_transpose (incidence a b)
  unfold Matrix.rank at hr
  omega

/-- A nonempty graph has at least the one-dimensional constant kernel.
No connectivity assumption is needed. -/
theorem vertex_kernel_pos (a b : E → V) (hv : Nonempty V) :
    0 < Module.finrank Bit (LinearMap.ker (incidence a b).mulVecLin) := by
  let c : Bit →ₗ[Bit] LinearMap.ker (incidence a b).mulVecLin :=
    { toFun z := ⟨fun _ => z, by
        change (incidence a b).mulVec (fun _ => z) = 0
        funext e
        simp [incidence_apply]⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hinj : Function.Injective c := by
    intro x y h
    obtain ⟨v⟩ := hv
    exact congrFun (congrArg Subtype.val h) v
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_self] at h
  omega

end Tantrix.FiniteGraph

namespace Tantrix.Grid

/-- The exact disconnected counting correction, obtained from the vertex
kernel dimension minus one. Geometrically this is the number of additional
components, but no component enumeration is needed by the reduction. -/
theorem exists_counting_correction (S : Support) (hs : S.Nonempty) (hn : NoHoles S) :
    ∃ b : ℕ,
      triangleCount S + (boundaryCount S + 2*b) + 2 = 2*S.card ∧
      (edgeCount S + b) + (boundaryCount S + 2*b) + 3 = 3*S.card := by
  have h1 := FiniteGraph.cycle_dimension_general (firstCell S) (lastCell S)
  rw [← incidence, filling_dimension S hn] at h1
  simp only [Fintype.card_coe] at h1
  change triangleCount S + S.card = edgeCount S +
    Module.finrank Bit (LinearMap.ker (incidence S).mulVecLin) at h1
  have hp := FiniteGraph.vertex_kernel_pos (firstCell S) (lastCell S)
    (show Nonempty (Cells S) from let ⟨p,hp⟩ := hs; ⟨⟨p,hp⟩⟩)
  change 0 < Module.finrank Bit (LinearMap.ker (incidence S).mulVecLin) at hp
  have h2 := contact_partition S
  have h3 := triangle_partition S
  refine ⟨Module.finrank Bit (LinearMap.ker (incidence S).mulVecLin)-1, ?_⟩
  unfold boundaryCount
  omega

/-- Every even network on any hole-free 56-cell support has at most 136 edges.
The support may have any number of connected components. -/
theorem score_le_136_of_no_holes (S : Support)
    (hn : NoHoles S) (h56 : S.card = 56)
    (x : Contacts S → Bit) (he : (decodeEdges S x).Even) :
    selectedCount S x ≤ 136 := by
  obtain ⟨b,hF,hE⟩ := exists_counting_correction S
    (Finset.card_pos.mp (by omega)) hn
  obtain ⟨y,hy⟩ := exists_maximum S
  have hsel := selection_partition S y
  have hwhole := whole_area_of_directed S (directed_area_bound S)
  obtain ⟨_,_,hphase⟩ := maximum_phase_estimates S hn y hy
  have hL : (0 : ℤ) ≤ boundaryCount S := Int.natCast_nonneg _
  have hd : (0 : ℤ) ≤ omittedCount S y := Int.natCast_nonneg _
  have hb : (0 : ℤ) ≤ b := Int.natCast_nonneg _
  have hphase' := hphase.trans
    (Tantrix.bridge_bound (boundaryCount S) (omittedCount S y) b hL hd hb)
  have hprod := mul_nonneg hb (add_nonneg hL hb)
  have hbound := Tantrix.score_le_136_of_estimates
    (triangleCount S) ((boundaryCount S : ℤ)+2*b)
    ((omittedCount S y : ℤ)+b) (selectedCount S y)
    (by omega) (by omega) (by omega) (by omega) (by nlinarith) hphase'
  have hnat : selectedCount S y ≤ 136 := by exact_mod_cast hbound
  exact (hy.2 x he).trans hnat

end Tantrix.Grid

namespace Tantrix.Loops
open Tantrix.Grid

/-- The scored coloured-loop upper bound without a connectedness assumption. -/
theorem score_le_136_of_no_holes {S : Support} {P : Placement S} (R : ScoredLoops P)
    (hn : NoHoles S) (h56 : S.card = 56) : score R ≤ 136 := by
  rw [← score_preserved R]
  exact Grid.score_le_136_of_no_holes S hn h56 (network R) (network_even R)

end Tantrix.Loops
