import Tantrix.Grid
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
open scoped BigOperators

namespace Tantrix.FiniteGraph
open Tantrix.Grid

variable {V E : Type*} [Fintype V] [DecidableEq V]

/-- A contact joins its two endpoints; edge indexing may be arbitrary. -/
def Adj (a b : E → V) (u v : V) : Prop :=
  ∃ e, (a e = u ∧ b e = v) ∨ (a e = v ∧ b e = u)

/-- Nonempty, with a finite contact walk between every two vertices. -/
def Connected (a b : E → V) : Prop :=
  Nonempty V ∧ ∀ u v, Relation.ReflTransGen (Adj a b) u v

def incidence (a b : E → V) : Matrix E V Bit :=
  fun e v => (if a e = v then 1 else 0) + (if b e = v then 1 else 0)

theorem incidence_apply (a b : E → V) (f : V → Bit) (e : E) :
    (incidence a b).mulVec f e = f (a e) + f (b e) := by
  simp [Matrix.mulVec, dotProduct, incidence, add_mul, Finset.sum_add_distrib]

theorem constant_of_kernel (a b : E → V) (hc : Connected a b)
    (f : V → Bit) (hf : (incidence a b).mulVec f = 0) (u v : V) : f u = f v := by
  have he : ∀ e, f (a e) = f (b e) := by
    intro e
    apply (bit_eq _ _).mp
    simpa only [incidence_apply, Pi.zero_apply] using congrFun hf e
  have hstep : ∀ x y, Adj a b x y → f x = f y := by
    rintro x y ⟨e, h | h⟩
    · rw [← h.1, ← h.2]; exact he e
    · rw [← h.1, ← h.2]; exact (he e).symm
  induction hc.2 u v with
  | refl => rfl
  | @tail v w path h ih => exact ih.trans (hstep v w h)

def constants : Bit →ₗ[Bit] (V → Bit) where
  toFun c := fun _ => c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem incidence_ker (a b : E → V) (hc : Connected a b) :
    LinearMap.ker (incidence a b).mulVecLin = LinearMap.range (constants (V := V)) := by
  ext f
  constructor
  · intro hf
    obtain ⟨v⟩ := hc.1
    refine ⟨f v, ?_⟩
    funext u
    exact constant_of_kernel a b hc f hf v u
  · rintro ⟨c, rfl⟩
    change (incidence a b).mulVec (fun _ => c) = 0
    funext e
    simp [incidence_apply]

/-- The parity-check kernel has one free bit per edge beyond a spanning tree.
This proof uses rank-nullity and finite walks, not a chosen spanning tree. -/
theorem cycle_dimension [Fintype E] (a b : E → V) (hc : Connected a b) :
    Module.finrank Bit (LinearMap.ker (incidence a b).transpose.mulVecLin) +
      Fintype.card V = Fintype.card E + 1 := by
  have hinj : Function.Injective (constants (V := V)) := by
    intro x y h
    obtain ⟨v⟩ := hc.1
    exact congrFun h v
  have hk : Module.finrank Bit (LinearMap.ker (incidence a b).mulVecLin) = 1 := by
    rw [incidence_ker a b hc, LinearMap.finrank_range_of_inj hinj]
    exact Module.finrank_self Bit
  have h1 := LinearMap.finrank_range_add_finrank_ker (K := Bit) (incidence a b).mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker (K := Bit) (incidence a b).transpose.mulVecLin
  rw [hk, Module.finrank_pi] at h1
  rw [Module.finrank_pi] at h2
  have hr := Matrix.rank_transpose (incidence a b)
  unfold Matrix.rank at hr
  omega

end Tantrix.FiniteGraph
