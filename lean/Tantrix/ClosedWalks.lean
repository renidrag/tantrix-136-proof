import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Tantrix.Algebra

/-!
# Balanced finite edge lists decompose into closed walks

Start with single-edge paths. Remove a closed path, or join an open path
to a path leaving its endpoint. Balance supplies a successor and each
operation reduces the number of paths. The resulting edge list is a
permutation of the original, so every edge occurrence is preserved.
-/

set_option autoImplicit false
open Classical
noncomputable section

namespace Tantrix.ClosedWalks

variable {E V : Type*}

def Follows (src dst : E → V) : V → List E → V → Prop
  | p, [], q => p = q
  | p, e :: es, q => src e = p ∧ Follows src dst (dst e) es q

theorem follows_append (src dst : E → V) (p q r : V) (a b : List E)
    (ha : Follows src dst p a q) (hb : Follows src dst q b r) :
    Follows src dst p (a ++ b) r := by
  induction a generalizing p with
  | nil =>
    change p = q at ha
    subst q
    exact hb
  | cons e a ih =>
    exact ⟨ha.1,ih (dst e) ha.2⟩

structure Walk (src dst : E → V) where
  start : V
  finish : V
  edges : List E
  follows : Follows src dst start edges finish

def Walk.single (src dst : E → V) (e : E) : Walk src dst :=
  ⟨src e,dst e,[e],⟨rfl,rfl⟩⟩

def Walk.join {src dst : E → V} (a b : Walk src dst) (h : a.finish = b.start) : Walk src dst where
  start := a.start
  finish := b.finish
  edges := a.edges ++ b.edges
  follows := follows_append src dst a.start a.finish b.finish a.edges b.edges a.follows
    (by rw [h]; exact b.follows)

def Walk.Closed {src dst : E → V} (a : Walk src dst) : Prop := a.finish = a.start

variable [DecidableEq V]

def Walk.flux {src dst : E → V} (a : Walk src dst) (v : V) : ℤ :=
  (if a.finish = v then 1 else 0) - (if a.start = v then 1 else 0)

def Balanced {src dst : E → V} (l : List (Walk src dst)) : Prop :=
  ∀ v, (l.map (fun a => a.flux v)).sum = 0

theorem closed_flux {src dst : E → V} (a : Walk src dst) (hc : a.Closed) (v : V) :
    a.flux v = 0 := by
  change a.finish = a.start at hc
  simp [Walk.flux,hc]

theorem join_flux {src dst : E → V} (a b : Walk src dst) (h : a.finish = b.start) (v : V) :
    (a.join b h).flux v = a.flux v + b.flux v := by
  by_cases h1 : b.finish = v <;> by_cases h2 : a.start = v <;> by_cases h3 : b.start = v <;>
    simp [Walk.flux,Walk.join,h,h1,h2,h3]

theorem balanced_tail {src dst : E → V} (a : Walk src dst) (l : List (Walk src dst))
    (hb : Balanced (a :: l)) (hc : a.Closed) : Balanced l := by
  intro v
  have h := hb v
  simpa only [List.map_cons,List.sum_cons,closed_flux a hc,zero_add] using h

theorem successor_exists {src dst : E → V} (a : Walk src dst) (l : List (Walk src dst))
    (hb : Balanced (a :: l)) (hc : ¬ a.Closed) :
    ∃ b ∈ l, b.start = a.finish := by
  by_contra hn
  push Not at hn
  have ha : a.flux a.finish = 1 := by
    have hne : a.start ≠ a.finish := fun h => hc h.symm
    simp [Walk.flux,hne]
  have hs : 0 ≤ (l.map (fun b => b.flux a.finish)).sum := by
    apply List.sum_nonneg
    intro n hn'
    obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hn'
    simp only [Walk.flux,hn b hb',ite_false,sub_zero]
    split_ifs <;> omega
  have h := hb a.finish
  simp only [List.map_cons,List.sum_cons,ha] at h
  omega

theorem balanced_join {src dst : E → V} (a b : Walk src dst)
    (x y : List (Walk src dst)) (hj : a.finish = b.start)
    (hb : Balanced (a :: (x ++ b :: y))) : Balanced (a.join b hj :: (x ++ y)) := by
  intro v
  have h := hb v
  simp only [List.map_cons,List.map_append,List.sum_cons,List.sum_append] at h ⊢
  rw [join_flux]
  omega

omit [DecidableEq V] in
theorem join_edge_perm {src dst : E → V} (a b : Walk src dst)
    (x y : List (Walk src dst)) (hj : a.finish = b.start) :
    ((a.join b hj :: (x ++ y)).flatMap Walk.edges).Perm
      ((a :: (x ++ b :: y)).flatMap Walk.edges) := by
  simp only [List.flatMap_cons,List.flatMap_append,Walk.join]
  simpa only [List.append_assoc] using
    ((List.perm_append_comm : (b.edges ++ x.flatMap Walk.edges).Perm
      (x.flatMap Walk.edges ++ b.edges)).append_left a.edges).append_right (y.flatMap Walk.edges)

theorem decompose_paths {src dst : E → V} (l : List (Walk src dst))
    (hb : Balanced l) : ∃ cycles : List (Walk src dst),
      (∀ c ∈ cycles, c.Closed) ∧
      (cycles.flatMap Walk.edges).Perm (l.flatMap Walk.edges) := by
  generalize hn : l.length = n
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
    cases l with
    | nil => exact ⟨[],by simp,by simp⟩
    | cons a l =>
      by_cases hc : a.Closed
      · obtain ⟨cs,hcs,hp⟩ := ih l.length (by simp only [List.length_cons] at hn; omega)
          l (balanced_tail a l hb hc) rfl
        refine ⟨a :: cs,?_,?_⟩
        · intro c hmem
          rcases List.mem_cons.mp hmem with rfl | hmem
          · exact hc
          · exact hcs c hmem
        · simpa only [List.flatMap_cons] using hp.append_left a.edges
      · obtain ⟨b,hbmem,hbj⟩ := successor_exists a l hb hc
        obtain ⟨x,y,hl⟩ := List.mem_iff_append.mp hbmem
        subst l
        have hj : a.finish = b.start := hbj.symm
        have hn : (a.join b hj :: (x ++ y)).length < (a :: (x ++ b :: y)).length := by simp
        obtain ⟨cs,hcs,hp⟩ := ih _ (by omega) _ (balanced_join a b x y hj hb) rfl
        exact ⟨cs,hcs,hp.trans (join_edge_perm a b x y hj)⟩

/-- Balance of a finite list of labelled directed edges. Repeated edge
occurrences, if present in the input, are retained with multiplicity. -/
def EdgeBalanced (src dst : E → V) (l : List E) : Prop :=
  ∀ v, (l.map (fun e => (if dst e = v then (1 : ℤ) else 0) -
    (if src e = v then 1 else 0))).sum = 0

theorem decompose_edges (src dst : E → V) (l : List E) (hb : EdgeBalanced src dst l) :
    ∃ cycles : List (Walk src dst), (∀ c ∈ cycles, c.Closed) ∧
      (cycles.flatMap Walk.edges).Perm l := by
  have hb' : Balanced (l.map (Walk.single src dst)) := by
    intro v
    change ((l.map (Walk.single src dst)).map (fun a => a.flux v)).sum = 0
    rw [List.map_map]
    have hlocal (e : E) : (Walk.single src dst e).flux v =
        (if dst e = v then (1 : ℤ) else 0) - (if src e = v then 1 else 0) := by
      unfold Walk.single Walk.flux
      split_ifs <;> rfl
    simp only [Function.comp_def,hlocal]
    exact hb v
  obtain ⟨cs,hcs,hp⟩ := decompose_paths _ hb'
  refine ⟨cs,hcs,?_⟩
  simpa only [List.flatMap_map,Function.comp_def,Walk.single,List.flatMap_singleton'] using hp

end Tantrix.ClosedWalks
