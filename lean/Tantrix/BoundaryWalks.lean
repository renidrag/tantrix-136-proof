import Tantrix.BoundaryEdges
import Tantrix.WalkArea

/-!
# Closed boundary words with exact area and counts

The oriented boundary is decomposed without assuming that the region is
connected, simply connected, or nonempty. Concatenating the closed vector
words keeps their signed areas additive. No joining edges are inserted.
-/

set_option autoImplicit false
open scoped BigOperators
open Classical
noncomputable section

namespace Tantrix.Area

def upSteps (w : List (Fin 6)) : ℤ :=
  (w.map (fun d => if d.val % 2 = 0 then (1 : ℤ) else 0)).sum
def downSteps (w : List (Fin 6)) : ℤ :=
  (w.map (fun d => if d.val % 2 = 1 then (1 : ℤ) else 0)).sum

/-- The purely six-direction statement, kept separate from boundary
assembly. Proved as `closed_word_area_bound` in `DirectionOrder.lean`. -/
def ClosedWordAreaBound : Prop := ∀ w : List (Fin 6),
  displacement (w.map direction) = 0 →
  9 * wordArea (w.map direction) ≤ Tantrix.areaNumerator (upSteps w) (downSteps w)

end Tantrix.Area

namespace Tantrix.Grid

open Tantrix.ClosedWalks

structure BoundaryWalkDecomposition (S : Support) (r : Triangles S → Bit) where
  walks : List (Walk (boundarySource S r) (boundaryTarget S r))
  closed : ∀ c ∈ walks, c.Closed
  inventory : (walks.flatMap Walk.edges).Perm (boundaryEnumeration S r)

/-- The original geometric vertex-balance theorem supplies every premise
of the general finite-edge decomposition. -/
theorem exists_boundary_walk_decomposition (S : Support) (r : Triangles S → Bit) :
    Nonempty (BoundaryWalkDecomposition S r) := by
  have hb : EdgeBalanced (boundarySource S r) (boundaryTarget S r) (boundaryEnumeration S r) := by
    intro p
    change ((boundaryEnumeration S r).map (fun e =>
      (if boundaryTarget S r e = p then (1 : ℤ) else 0) -
      (if boundarySource S r e = p then 1 else 0))).sum = 0
    rw [boundaryEnumeration,Finset.sum_map_toList]
    exact boundary_flux_sum S r p
  obtain ⟨cs,hc,hp⟩ := decompose_edges (boundarySource S r) (boundaryTarget S r) _ hb
  exact ⟨⟨cs,hc,hp⟩⟩

theorem boundary_vector_map (S : Support) (r : Triangles S → Bit) (l : List (BoundaryEdges S r)) :
    (l.map (boundaryDirection S r)).map Tantrix.Area.direction =
      l.map (step (boundarySource S r) (boundaryTarget S r)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro e _
  exact (boundary_step S r e).symm

namespace BoundaryWalkDecomposition

variable {S : Support} {r : Triangles S → Bit} (D : BoundaryWalkDecomposition S r)

def words : List (List (Fin 6)) := D.walks.map (fun c => c.edges.map (boundaryDirection S r))
def word : List (Fin 6) := D.words.flatten

theorem word_eq : D.word = (D.walks.flatMap Walk.edges).map (boundaryDirection S r) := by
  simp only [word,words,List.flatMap_def,List.map_flatten,List.map_map,Function.comp_def]

/-- Every boundary contact occurs exactly once across all the walks. -/
theorem edges_nodup : (D.walks.flatMap Walk.edges).Nodup :=
  D.inventory.nodup_iff.mpr (Finset.nodup_toList _)

theorem words_closed : ∀ w ∈ D.words, Tantrix.Area.displacement (w.map Tantrix.Area.direction) = 0 := by
  intro w hw
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hw
  rw [boundary_vector_map]
  exact closed_walk_displacement _ _ c (D.closed c hc)

theorem word_closed : Tantrix.Area.displacement (D.word.map Tantrix.Area.direction) = 0 := by
  rw [word_eq,boundary_vector_map]
  exact collection_displacement _ _ D.walks D.closed

/-- The entire six-direction multiset, not just total length, is unchanged. -/
theorem direction_inventory : D.word.Perm ((boundaryEnumeration S r).map (boundaryDirection S r)) := by
  rw [word_eq]
  exact D.inventory.map _

theorem direction_count (d : Fin 6) :
    D.word.count d = ((boundaryEnumeration S r).map (boundaryDirection S r)).count d :=
  D.direction_inventory.count_eq d

theorem word_weight (f : Fin 6 → ℤ) :
    (D.word.map f).sum = ∑ e : BoundaryEdges S r, f (boundaryDirection S r e) := by
  rw [(D.direction_inventory.map f).sum_eq,List.map_map]
  exact Finset.sum_map_toList _ _

theorem word_area : Tantrix.Area.wordArea (D.word.map Tantrix.Area.direction) = regionArea S r := by
  rw [word_eq,boundary_vector_map,collection_area _ _ D.walks D.closed]
  unfold integral
  rw [(D.inventory.map (fun e => Tantrix.Area.det (boundarySource S r e) (boundaryTarget S r e))).sum_eq]
  rw [boundaryEnumeration,Finset.sum_map_toList]
  exact boundary_area_sum S r

theorem word_up : Tantrix.Area.upSteps D.word = directedUp S r := by
  rw [Tantrix.Area.upSteps,word_weight]
  exact boundary_even_sum S r

theorem word_down : Tantrix.Area.downSteps D.word = directedDown S r := by
  rw [Tantrix.Area.downSteps,word_weight]
  exact boundary_odd_sum S r

end BoundaryWalkDecomposition

/-- A finite family of closed boundary words, with exact signed area and
both directed counts after concatenation. -/
theorem region_boundary_words (S : Support) (r : Triangles S → Bit) :
    ∃ words : List (List (Fin 6)),
      (∀ w ∈ words, Tantrix.Area.displacement (w.map Tantrix.Area.direction) = 0) ∧
      Tantrix.Area.wordArea (words.flatten.map Tantrix.Area.direction) = regionArea S r ∧
      Tantrix.Area.upSteps words.flatten = directedUp S r ∧
      Tantrix.Area.downSteps words.flatten = directedDown S r := by
  obtain ⟨D⟩ := exists_boundary_walk_decomposition S r
  exact ⟨D.words,D.words_closed,D.word_area,D.word_up,D.word_down⟩

/-- The interface needed for rearrangement: a closed six-direction word
with exactly the region's area and directed boundary counts. -/
theorem region_boundary_word (S : Support) (r : Triangles S → Bit) :
    ∃ w : List (Fin 6),
      Tantrix.Area.displacement (w.map Tantrix.Area.direction) = 0 ∧
      Tantrix.Area.wordArea (w.map Tantrix.Area.direction) = regionArea S r ∧
      Tantrix.Area.upSteps w = directedUp S r ∧
      Tantrix.Area.downSteps w = directedDown S r := by
  obtain ⟨D⟩ := exists_boundary_walk_decomposition S r
  exact ⟨D.word,D.word_closed,D.word_area,D.word_up,D.word_down⟩

/-- No boundary-assembly or phase-data premise remains once the independent
closed-word inequality has been supplied. -/
theorem directed_area_of_closed_word_bound (h : Tantrix.Area.ClosedWordAreaBound) (S : Support) :
    DirectedAreaBound S := by
  intro r
  obtain ⟨w,hc,ha,hp,hq⟩ := region_boundary_word S r
  have hw := h w hc
  rwa [ha,hp,hq] at hw

end Tantrix.Grid
