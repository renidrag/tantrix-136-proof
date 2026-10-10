import Tantrix.ClosedWalks
import Tantrix.AreaWords

/-!
# Area and displacement of labelled closed walks

This module connects endpoint-following walks with the existing vector-word
area. It uses exact integer coordinates and does not assume simplicity.
-/

set_option autoImplicit false

namespace Tantrix.ClosedWalks

open Tantrix.Area
variable {E : Type*}

def step (src dst : E → Vector) (e : E) : Vector := dst e - src e
def integral (src dst : E → Vector) (l : List E) : ℤ :=
  (l.map (fun e => det (src e) (dst e))).sum

theorem follows_displacement (src dst : E → Vector) (p q : Vector) (l : List E)
    (h : Follows src dst p l q) : displacement (l.map (step src dst)) = q-p := by
  induction l generalizing p with
  | nil =>
    change p = q at h
    subst q
    simp [displacement]
  | cons e l ih =>
    have hr := ih (dst e) h.2
    simp only [List.map_cons,displacement_cons,hr,step]
    rw [h.1]
    ext <;> simp

theorem follows_edgeArea (src dst : E → Vector) (p q : Vector) (l : List E)
    (h : Follows src dst p l q) : edgeArea p (l.map (step src dst)) = integral src dst l := by
  induction l generalizing p with
  | nil => rfl
  | cons e l ih =>
    have hp : p + step src dst e = dst e := by
      rw [← h.1]
      ext <;> simp [step]
    simp only [List.map_cons,edgeArea,hp,ih (dst e) h.2,integral,List.sum_cons]
    rw [h.1]

theorem closed_walk_displacement (src dst : E → Vector) (c : Walk src dst) (hc : c.Closed) :
    displacement (c.edges.map (step src dst)) = 0 := by
  rw [follows_displacement src dst c.start c.finish c.edges c.follows]
  change c.finish = c.start at hc
  rw [hc,sub_self]

theorem closed_walk_area (src dst : E → Vector) (c : Walk src dst) (hc : c.Closed) :
    wordArea (c.edges.map (step src dst)) = integral src dst c.edges := by
  have h := follows_edgeArea src dst c.start c.finish c.edges c.follows
  rwa [closed_edgeArea c.start _ (closed_walk_displacement src dst c hc)] at h

theorem collection_displacement (src dst : E → Vector) (cs : List (Walk src dst))
    (hc : ∀ c ∈ cs, c.Closed) :
    displacement ((cs.flatMap Walk.edges).map (step src dst)) = 0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have h0 := closed_walk_displacement src dst c (hc c List.mem_cons_self)
    have h1 := ih (fun a ha => hc a (List.mem_cons_of_mem _ ha))
    simp only [List.flatMap_cons,List.map_append,displacement_append,h0,h1,add_zero]

theorem collection_area (src dst : E → Vector) (cs : List (Walk src dst))
    (hc : ∀ c ∈ cs, c.Closed) :
    wordArea ((cs.flatMap Walk.edges).map (step src dst)) =
      integral src dst (cs.flatMap Walk.edges) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc0 := hc c List.mem_cons_self
    have h0 := closed_walk_area src dst c hc0
    have h1 := ih (fun a ha => hc a (List.mem_cons_of_mem _ ha))
    simp only [List.flatMap_cons,List.map_append,wordArea_append,
      closed_walk_displacement src dst c hc0,det_zero_left,add_zero,h0,h1,
      integral,List.sum_append]

end Tantrix.ClosedWalks
