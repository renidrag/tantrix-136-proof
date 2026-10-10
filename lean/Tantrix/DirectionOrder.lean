import Tantrix.Rearrangement
import Tantrix.BoundaryWalks

/-!
# Direction ordering and the complete directed area inequality

Every lexicographically least closed maximizer is sorted. Descending
adjacent labels must have strictly positive swap cost. Two block-swap
inequalities forbid skipping an earlier occurring direction. This handles
zero-area words too, without collinearity, reversals or turn-counting.
The directed inequality is then sorting followed by the two-square bound.
-/

set_option autoImplicit false

namespace Tantrix.Area

variable {α : Type*}

/-- If descending adjacent labels had zero swap cost, swapping them would
preserve maximal area and improve the lexicographic tie-break. -/
theorem lex_descent_det_pos [LinearOrder α] (f : α → Vector) (x y : List α) (u v : α)
    (hm : IsAreaMaximum f (x ++ [u] ++ [v] ++ y))
    (hmin : ∀ z, z.Perm (x ++ [u] ++ [v] ++ y) →
      areaOf f z = areaOf f (x ++ [u] ++ [v] ++ y) → x ++ [u] ++ [v] ++ y ≤ z)
    (hvu : v < u) : 0 < det (f u) (f v) := by
  have hs := lex_swap_det_pos f x [u] [v] y hm hmin (by
    change List.Lex (· < ·) _ _
    simp only [List.append_assoc,List.singleton_append]
    exact List.Lex.append_left _ (.rel hvu) x)
  simpa [displacementOf,displacement] using hs

/-- Two block-swap inequalities forbid skipping a step which is the sum
of two consecutive positively turning steps. Closure is not needed. -/
theorem maximum_no_skipped_step (f : α → Vector) (u v t : α) (x y : List α)
    (hm : IsAreaMaximum f ([t] ++ x ++ [u] ++ [v] ++ y))
    (ht : f t = f u + f v) (hd : 0 < det (f u) (f v)) : False := by
  have h1 := maximum_block_det f [] [t] (x ++ [u]) ([v] ++ y)
    (by simpa only [List.nil_append,List.append_assoc] using hm)
  have h2 := maximum_block_det f [t] x ([u] ++ [v]) y
    (by simpa only [List.append_assoc] using hm)
  simp only [displacementOf,List.map_append,displacement_append,List.map_singleton,
    displacement_cons,displacement_nil,add_zero] at h1 h2
  rw [ht] at h1
  simp only [det,Prod.fst_add,Prod.snd_add] at h1 h2 hd
  nlinarith

theorem displacementOf_perm (f : α → Vector) {a b : List α} (h : a.Perm b) :
    displacementOf f a = displacementOf f b := (h.map f).sum_eq

theorem RunGrouped.tail {a : α} {w : List α} (h : RunGrouped (a :: w)) : RunGrouped w := by
  intro x b y u v hw
  exact h (a :: x) b y u v (by simp [hw])

/-- Returning to the first symbol after a different symbol would split its run. -/
theorem RunGrouped.return_to_head (a b : α) (x y : List α)
    (h : RunGrouped ([a] ++ x ++ [b] ++ [a] ++ y)) : a = b := by
  induction x with
  | nil => exact h [] [] y a b (by simp)
  | cons c x ih =>
    have he : a = c := h [] (x ++ [b]) y a c (by simp)
    subst c
    apply ih
    apply RunGrouped.tail (a := a)
    simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using h

/-- Rotating a smaller occurring symbol to the front would improve the
lexicographic tie-break, so a least closed maximizer starts at its minimum. -/
theorem lex_minimum_head [LinearOrder α] (f : α → Vector) (a : α) (w : List α)
    (hc : displacementOf f (a :: w) = 0)
    (hmin : ∀ v, v.Perm (a :: w) → areaOf f v = areaOf f (a :: w) → a :: w ≤ v) :
    ∀ b ∈ w, a ≤ b := by
  intro b hb
  obtain ⟨x,y,hw⟩ := List.mem_iff_append.mp hb
  subst w
  have he := areaOf_rotate f (a :: x) (b :: y)
    (by simpa only [List.cons_append] using hc)
  have hp : ((b :: y) ++ (a :: x)).Perm (a :: (x ++ b :: y)) := by
    simpa only [List.cons_append] using
      (List.perm_append_comm : ((b :: y) ++ (a :: x)).Perm ((a :: x) ++ (b :: y)))
  have hh := hmin _ hp (by simpa only [List.cons_append] using he)
  by_contra hn
  have hl : (b :: (y ++ a :: x)) < (a :: (x ++ b :: y)) := by
    change List.Lex (· < ·) _ _
    exact List.Lex.rel (lt_of_not_ge hn)
  exact (not_lt_of_ge hh) hl

/-- A descending transition with strictly positive determinant either
returns to zero or is the jump 5 to 1. -/
theorem descending_transition (i j : Fin 6) (hji : j < i)
    (hd : 0 < det (direction i) (direction j)) :
    j = 0 ∨ (i = 5 ∧ j = 1) := by
  fin_cases i <;> fin_cases j <;> norm_num [direction,det] at *

/-- Every lexicographically least closed maximizer is sorted, including
zero-area words. No collinearity or reversal case is needed. -/
theorem lex_maximum_sorted (z : List (Fin 6))
    (hm : IsAreaMaximum direction z) (hc : displacementOf direction z = 0)
    (hmin : ∀ v, v.Perm z → areaOf direction v = areaOf direction z → z ≤ v) :
    z.Pairwise (· ≤ ·) := by
  have hg := lex_minimum_runGrouped direction z hm hmin
  have hadj : ∀ (x y : List (Fin 6)) (i j : Fin 6),
      z = x ++ [i] ++ [j] ++ y → i ≤ j := by
    intro x y i j hz
    subst z
    by_contra hn
    have hji : j < i := lt_of_not_ge hn
    have hd := lex_descent_det_pos direction x y i j hm hmin hji
    rcases descending_transition i j hji hd with hzero | ⟨rfl,rfl⟩
    · subst j
      cases x with
      | nil =>
        have hh := lex_minimum_head direction i (0 :: y)
          (by simpa using hc) (by simpa using hmin) 0 (by simp)
        exact hn hh
      | cons m x =>
        have hh := lex_minimum_head direction m (x ++ [i] ++ [0] ++ y)
          (by simpa using hc) (by simpa using hmin) 0 (by simp)
        have he : m = 0 := le_antisymm hh (Fin.zero_le _)
        subst m
        have hi := RunGrouped.return_to_head 0 i x y (by simpa using hg)
        subst i
        exact hn le_rfl
    · cases x with
      | nil =>
        have hh := lex_minimum_head direction 5 (1 :: y)
          (by simpa using hc) (by simpa using hmin) 1 (by simp)
        exact hn hh
      | cons m x =>
        have hh := lex_minimum_head direction m (x ++ [5] ++ [1] ++ y)
          (by simpa using hc) (by simpa using hmin) 1 (by simp)
        have hm01 : m = 0 ∨ m = 1 := by
          fin_cases m <;> norm_num at *
        rcases hm01 with rfl | rfl
        · exact maximum_no_skipped_step direction 5 1 0 x y
            (by simpa using hm) (by decide) (by decide)
        · have hi := RunGrouped.return_to_head 1 5 x y (by simpa using hg)
          exact (by decide : (1 : Fin 6) ≠ 5) hi
  have chain : z.IsChain (· ≤ ·) := by
    clear hm hc hmin hg
    induction z with
    | nil => simp
    | cons a w ih =>
      cases w with
      | nil => simp
      | cons b w =>
        rw [List.isChain_cons_cons]
        refine ⟨hadj [] w a b (by simp),?_⟩
        apply ih
        intro x y i j he
        exact hadj (a :: x) y i j (by simp [he])
  exact chain.pairwise

/-- The canonical six direction blocks, allowing zero counts. -/
def sortedDirections (w : List (Fin 6)) : List (Fin 6) :=
  List.replicate (w.count 0) 0 ++ List.replicate (w.count 1) 1 ++
  List.replicate (w.count 2) 2 ++ List.replicate (w.count 3) 3 ++
  List.replicate (w.count 4) 4 ++ List.replicate (w.count 5) 5

theorem sortedDirections_perm (w : List (Fin 6)) : (sortedDirections w).Perm w := by
  apply List.perm_iff_count.mpr
  intro d
  fin_cases d <;> simp [sortedDirections,List.count_replicate]

theorem sortedDirections_pairwise (w : List (Fin 6)) :
    (sortedDirections w).Pairwise (· ≤ ·) := by
  simp [sortedDirections,List.pairwise_append,List.pairwise_replicate,List.mem_replicate,
    or_imp,forall_and]

theorem sortedDirections_map (w : List (Fin 6)) :
    (sortedDirections w).map direction =
      sortedWord (w.count 0) (w.count 1) (w.count 2) (w.count 3) (w.count 4) (w.count 5) := by
  simp [sortedDirections,sortedWord,List.map_append,List.map_replicate]

theorem sortedDirections_up (w : List (Fin 6)) :
    upSteps (sortedDirections w) = (w.count 0 : ℤ) + w.count 2 + w.count 4 := by
  simp [upSteps,sortedDirections,List.sum_append,List.sum_replicate,add_assoc]

theorem sortedDirections_down (w : List (Fin 6)) :
    downSteps (sortedDirections w) = (w.count 1 : ℤ) + w.count 3 + w.count 5 := by
  simp [downSteps,sortedDirections,List.sum_append,List.sum_replicate,add_assoc]

theorem upSteps_perm {v w : List (Fin 6)} (hp : v.Perm w) : upSteps v = upSteps w :=
  (hp.map _).sum_eq

theorem downSteps_perm {v w : List (Fin 6)} (hp : v.Perm w) : downSteps v = downSteps w :=
  (hp.map _).sum_eq

/-- Sorting a closed word cannot decrease its area. This includes the
degenerate and negative-area cases without a separate argument. -/
theorem word_area_le_sorted (w : List (Fin 6)) (hw : displacementOf direction w = 0) :
    areaOf direction w ≤ areaOf direction (sortedDirections w) := by
  obtain ⟨v,hp,hm,hmin⟩ := exists_lex_area_maximum direction w
  have hc := (displacementOf_perm direction hp).trans hw
  have hs := lex_maximum_sorted v hm hc hmin
  have he : v = sortedDirections w := List.Perm.eq_of_pairwise
    (fun _ _ _ _ hab hba => le_antisymm hab hba) hs (sortedDirections_pairwise w)
    (hp.trans (sortedDirections_perm w).symm)
  simpa only [he] using hm w hp.symm

/-- The directed inequality is sorting followed by the two-square bound. -/
theorem closed_word_area_bound : ClosedWordAreaBound := by
  intro w hw
  have hm := word_area_le_sorted w hw
  have hc : displacement ((sortedDirections w).map direction) = 0 :=
    (displacementOf_perm direction (sortedDirections_perm w)).trans hw
  have hb := sorted_word_bound (w.count 0) (w.count 1) (w.count 2)
    (w.count 3) (w.count 4) (w.count 5) (by rwa [← sortedDirections_map])
  rw [← sortedDirections_map,← sortedDirections_up,← sortedDirections_down,
    upSteps_perm (sortedDirections_perm w),downSteps_perm (sortedDirections_perm w)] at hb
  change areaOf direction w ≤ wordArea ((sortedDirections w).map direction) at hm
  change 9 * areaOf direction w ≤ _
  omega

end Tantrix.Area

namespace Tantrix.Grid

/-- The directed area inequality follows from the explicit region
boundary construction and the proved closed-word bound, with no geometric
inequality supplied as a hypothesis. -/
theorem directed_area_bound (S : Support) : DirectedAreaBound S :=
  directed_area_of_closed_word_bound Tantrix.Area.closed_word_area_bound S

end Tantrix.Grid
