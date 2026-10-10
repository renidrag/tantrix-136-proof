import Tantrix.Algebra
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fin.VecNotation

/-!
# Determinant area of lattice words

These identities hold for arbitrary integer vectors, not only simple
polygons. They are the algebraic interface for boundary rearrangement.
-/

set_option autoImplicit false

namespace Tantrix.Area

abbrev Vector := ℤ × ℤ

def det (u v : Vector) : ℤ := u.1 * v.2 - u.2 * v.1

@[simp] theorem det_zero_left (v : Vector) : det 0 v = 0 := by simp [det]
@[simp] theorem det_zero_right (v : Vector) : det v 0 = 0 := by simp [det]
@[simp] theorem det_self (v : Vector) : det v v = 0 := by unfold det; ring
theorem det_add_left (u v w : Vector) : det (u+v) w = det u w + det v w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring
theorem det_add_right (u v w : Vector) : det u (v+w) = det u v + det u w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring
theorem det_antisymm (u v : Vector) : det u v = -det v u := by
  unfold det; ring

/-- Displacement of a word of vectors. -/
def displacement (w : List Vector) : Vector := w.sum

/-- Signed area in units of an elementary lattice triangle. -/
def wordArea : List Vector → ℤ
  | [] => 0
  | u :: w => det u (displacement w) + wordArea w

@[simp] theorem displacement_nil : displacement [] = 0 := rfl
@[simp] theorem displacement_cons (u : Vector) (w : List Vector) :
    displacement (u :: w) = u + displacement w := rfl
theorem displacement_append (u v : List Vector) :
    displacement (u ++ v) = displacement u + displacement v := List.sum_append

theorem wordArea_append (u v : List Vector) :
    wordArea (u ++ v) = wordArea u + wordArea v + det (displacement u) (displacement v) := by
  induction u with
  | nil => simp [wordArea]
  | cons a u ih =>
    simp only [List.cons_append, wordArea, displacement_append, displacement_cons,
      det_add_left, det_add_right, ih]
    ring

/-- A closed block can be moved across a cut without changing area. -/
theorem wordArea_rotate (u v : List Vector) (hc : displacement (u ++ v) = 0) :
    wordArea (v ++ u) = wordArea (u ++ v) := by
  have hs : displacement v = -displacement u := by
    rw [displacement_append] at hc
    exact eq_neg_of_add_eq_zero_right hc
  rw [wordArea_append, wordArea_append, hs]
  simp [det, displacement]
  ring

theorem wordArea_closed_append (u v : List Vector)
    (hu : displacement u = 0) (hv : displacement v = 0) :
    wordArea (u ++ v) = wordArea u + wordArea v := by
  simp [wordArea_append, hu, hv]

/-- Exchanging adjacent blocks changes area by twice their determinant. -/
theorem wordArea_swap (x u v y : List Vector) :
    wordArea (x ++ v ++ u ++ y) - wordArea (x ++ u ++ v ++ y) =
      -2 * det (displacement u) (displacement v) := by
  simp only [wordArea_append, displacement_append, det_add_left]
  rw [det_antisymm (displacement v) (displacement u)]
  ring

/-- The same word traced from a specified starting point. -/
def edgeArea (p : Vector) : List Vector → ℤ
  | [] => 0
  | v :: w => det p (p+v) + edgeArea (p+v) w

theorem edgeArea_eq (p : Vector) (w : List Vector) :
    edgeArea p w = wordArea w + det p (displacement w) := by
  induction w generalizing p with
  | nil => simp [edgeArea, wordArea]
  | cons v w ih =>
    simp only [edgeArea, wordArea, ih, displacement_cons, det_add_left,
      det_add_right, det_self]
    ring

theorem closed_edgeArea (p : Vector) (w : List Vector) (hc : displacement w = 0) :
    edgeArea p w = wordArea w := by simp [edgeArea_eq, hc]

/-- The six counterclockwise lattice directions. -/
def direction : Fin 6 → Vector := ![(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]

theorem displacement_replicate (n : ℕ) (v : Vector) :
    displacement (List.replicate n v) = ((n : ℤ)*v.1,(n : ℤ)*v.2) := by
  induction n with
  | zero => ext <;> simp [displacement]
  | succ n ih =>
    rw [List.replicate_succ,displacement_cons,ih]
    ext <;> simp <;> ring

theorem wordArea_replicate (n : ℕ) (v : Vector) :
    wordArea (List.replicate n v) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ,wordArea,ih,displacement_replicate]
    simp only [det,add_zero]
    ring

def sortedWord (a b c d e f : ℕ) : List Vector :=
  List.replicate a (direction 0) ++ List.replicate b (direction 1) ++
  List.replicate c (direction 2) ++ List.replicate d (direction 3) ++
  List.replicate e (direction 4) ++ List.replicate f (direction 5)

theorem sorted_displacement (a b c d e f : ℕ) :
    displacement (sortedWord a b c d e f) =
      ((a : ℤ)-c-d+f,(b : ℤ)+c-e-f) := by
  simp [sortedWord,displacement_append,displacement_replicate,direction]
  constructor <;> ring

theorem sorted_wordArea (a b c d e f : ℕ)
    (hc : displacement (sortedWord a b c d e f) = 0) :
    wordArea (sortedWord a b c d e f) =
      2*((a : ℤ)+b)*(c+d)-(a : ℤ)^2-(d : ℤ)^2 := by
  have h := sorted_displacement a b c d e f
  rw [hc] at h
  have he : (e : ℤ) = a+b-d := by
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_zero,Prod.snd_zero] at h1 h2
    omega
  have hf : (f : ℤ) = c+d-a := by
    have h1 := congrArg Prod.fst h
    simp only [Prod.fst_zero] at h1
    omega
  simp only [sortedWord,wordArea_append,wordArea_replicate,displacement_append,
    displacement_replicate]
  norm_num [direction,det]
  rw [he,hf]
  ring

/-- The directed inequality for an actual direction-sorted closed word.
The extension to arbitrary closed words is proved in `DirectionOrder.lean`. -/
theorem sorted_word_bound (a b c d e f : ℕ)
    (hc : displacement (sortedWord a b c d e f) = 0) :
    9 * wordArea (sortedWord a b c d e f) ≤
      Tantrix.areaNumerator ((a : ℤ)+c+e) ((b : ℤ)+d+f) := by
  have h := sorted_displacement a b c d e f
  rw [hc] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.fst_zero,Prod.snd_zero] at h1 h2
  have he : (e : ℤ) = a+b-d := by omega
  have hf : (f : ℤ) = c+d-a := by omega
  rw [sorted_wordArea a b c d e f hc,he,hf]
  exact Tantrix.sorted_area_bound a b c d

end Tantrix.Area
