import Tantrix.AreaWords
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Permutation
import Mathlib.Data.Finset.Max

/-!
# Area-maximizing rearrangements

For a fixed finite multiset of vectors, an area-maximizing ordering exists.
Its block-swap inequalities are consequences of maximality, not geometric
assumptions. Among maximizers, lexicographic minimization groups repeated
directions into a single run.
-/

set_option autoImplicit false

namespace Tantrix.Area

variable {α : Type*}

def areaOf (f : α → Vector) (w : List α) : ℤ := wordArea (w.map f)
def displacementOf (f : α → Vector) (w : List α) : Vector := displacement (w.map f)

def IsAreaMaximum (f : α → Vector) (w : List α) : Prop :=
  ∀ v, v.Perm w → areaOf f v ≤ areaOf f w

theorem areaOf_swap (f : α → Vector) (x u v y : List α) :
    areaOf f (x ++ v ++ u ++ y) - areaOf f (x ++ u ++ v ++ y) =
      -2 * det (displacementOf f u) (displacementOf f v) := by
  simpa only [areaOf,displacementOf,List.map_append] using
    wordArea_swap (x.map f) (u.map f) (v.map f) (y.map f)

theorem areaOf_rotate (f : α → Vector) (u v : List α)
    (hc : displacementOf f (u ++ v) = 0) : areaOf f (v ++ u) = areaOf f (u ++ v) := by
  simp only [areaOf,List.map_append]
  apply wordArea_rotate (u.map f) (v.map f)
  simpa only [displacementOf,List.map_append] using hc

theorem exists_area_maximum (f : α → Vector) (w : List α) :
    ∃ v, v.Perm w ∧ IsAreaMaximum f v := by
  classical
  let candidates := w.permutations.toFinset
  have hn : candidates.Nonempty := ⟨w, by simp [candidates,List.mem_permutations]⟩
  obtain ⟨v,hv,hm⟩ := Finset.exists_max_image candidates (areaOf f) hn
  have hp : v.Perm w := List.mem_permutations.mp (List.mem_toFinset.mp hv)
  refine ⟨v,hp,?_⟩
  intro z hz
  exact hm z (List.mem_toFinset.mpr (List.mem_permutations.mpr (hz.trans hp)))

theorem block_swap_perm (x u v y : List α) :
    (x ++ v ++ u ++ y).Perm (x ++ u ++ v ++ y) := by
  simpa only [List.append_assoc] using
    ((List.perm_append_comm : (v ++ u).Perm (u ++ v)).append_left x).append_right y

theorem maximum_block_det (f : α → Vector) (x u v y : List α)
    (hm : IsAreaMaximum f (x ++ u ++ v ++ y)) :
    0 ≤ det (displacementOf f u) (displacementOf f v) := by
  have h := hm (x ++ v ++ u ++ y) (block_swap_perm x u v y)
  have hs := areaOf_swap f x u v y
  omega

/-- A lexicographically improving block swap must strictly lose area;
otherwise it contradicts maximal area or its tie-break. -/
theorem lex_swap_det_pos [LinearOrder α] (f : α → Vector) (x u v y : List α)
    (hm : IsAreaMaximum f (x ++ u ++ v ++ y))
    (hmin : ∀ z, z.Perm (x ++ u ++ v ++ y) →
      areaOf f z = areaOf f (x ++ u ++ v ++ y) → x ++ u ++ v ++ y ≤ z)
    (hl : x ++ v ++ u ++ y < x ++ u ++ v ++ y) :
    0 < det (displacementOf f u) (displacementOf f v) := by
  have hd := maximum_block_det f x u v y hm
  have hs := areaOf_swap f x u v y
  by_contra hn
  have he : areaOf f (x ++ v ++ u ++ y) = areaOf f (x ++ u ++ v ++ y) := by omega
  exact (not_lt_of_ge (hmin _ (block_swap_perm x u v y) he)) hl

theorem exists_lex_area_maximum [LinearOrder α] (f : α → Vector) (w : List α) :
    ∃ v, v.Perm w ∧ IsAreaMaximum f v ∧
      ∀ z, z.Perm v → areaOf f z = areaOf f v → v ≤ z := by
  classical
  obtain ⟨m,hmp,hm⟩ := exists_area_maximum f w
  let candidates := w.permutations.toFinset.filter (fun v => areaOf f v = areaOf f m)
  have hn : candidates.Nonempty := ⟨m, by simp [candidates,List.mem_permutations,hmp]⟩
  obtain ⟨v,hv,hmin⟩ := Finset.exists_min_image candidates id hn
  have hp : v.Perm w := List.mem_permutations.mp (List.mem_toFinset.mp (Finset.mem_filter.mp hv).1)
  have ha : areaOf f v = areaOf f m := (Finset.mem_filter.mp hv).2
  refine ⟨v,hp,?_,?_⟩
  · intro z hz
    rw [ha]
    exact hm z ((hz.trans hp).trans hmp.symm)
  · intro z hz harea
    exact hmin z (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
      (List.mem_permutations.mpr (hz.trans hp)),harea.trans ha⟩)

theorem move_left_lex [LinearOrder α] (x a y : List α) (u v : α) (h : u < v) :
    x ++ [u] ++ [u] ++ (v :: a) ++ y < x ++ [u] ++ (v :: a) ++ [u] ++ y := by
  change List.Lex (· < ·) _ _
  simp only [List.append_assoc,List.cons_append]
  exact List.Lex.append_left _ (.cons (.rel h)) x

theorem move_right_lex [LinearOrder α] (x a y : List α) (u v : α) (h : v < u) :
    x ++ (v :: a) ++ [u] ++ [u] ++ y < x ++ [u] ++ (v :: a) ++ [u] ++ y := by
  change List.Lex (· < ·) _ _
  simp only [List.append_assoc,List.cons_append]
  exact List.Lex.append_left _ (.rel h) x

/-- Once a word leaves one symbol for a different one, it never returns to
the first symbol. Equivalently, each occurring symbol has just one run. -/
def RunGrouped (w : List α) : Prop :=
  ∀ (x a y : List α) (u v : α), w = x ++ [u] ++ (v :: a) ++ [u] ++ y → u = v

/-- Every lexicographically least area maximizer groups equal directions. -/
theorem lex_minimum_runGrouped [LinearOrder α] (f : α → Vector) (z : List α)
    (hm : IsAreaMaximum f z)
    (hmin : ∀ v, v.Perm z → areaOf f v = areaOf f z → z ≤ v) : RunGrouped z := by
  intro x a y u v hz
  subst z
  by_contra hne
  have h1 := maximum_block_det f x [u] (v :: a) ([u] ++ y)
    (by simpa only [List.append_assoc] using hm)
  have h2 := maximum_block_det f (x ++ [u]) (v :: a) [u] y hm
  rw [det_antisymm] at h2
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hs := lex_swap_det_pos f (x ++ [u]) (v :: a) [u] y hm hmin
      (move_left_lex x a y u v hlt)
    rw [det_antisymm] at hs
    omega
  · have hs := lex_swap_det_pos f x [u] (v :: a) ([u] ++ y)
      (by simpa only [List.append_assoc] using hm)
      (by simpa only [List.append_assoc] using hmin)
      (by simpa only [List.append_assoc] using move_right_lex x a y u v hgt)
    omega

/-- A maximum-area ordering with no repeated direction runs always exists.
This works for arbitrary vectors and does not require a simple polygon. -/
theorem exists_grouped_area_maximum [LinearOrder α] (f : α → Vector) (w : List α) :
    ∃ v, v.Perm w ∧ IsAreaMaximum f v ∧ RunGrouped v := by
  obtain ⟨z,hp,hm,hmin⟩ := exists_lex_area_maximum f w
  exact ⟨z,hp,hm,lex_minimum_runGrouped f z hm hmin⟩

end Tantrix.Area
