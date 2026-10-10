import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Triangular lattice fillings and the no-holes condition

Tile centres are integer coordinate pairs with six side-neighbours.
Three parity fields encode the undirected horizontal, vertical and diagonal
contacts. Up/down triangle fields encode subsets of elementary triangles.

Finite even networks have unique finite fillings, constructed by finite
column prefix sums. The no-holes hypothesis is defined independently as
escape by a finite empty-cell walk from every finite coordinate box.
It implies containment of the filling in the occupied triangles.

The final boundary_bijective theorem proves the filling correspondence.
There are no area estimates, Euler formulas, or graph-counting assumptions.
The bounded-coordinate definitions of finiteness are proved equivalent to
ordinary finite support.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Tantrix.Grid

abbrev Bit := ZMod 2
abbrev Vertex := ℤ × ℤ

@[simp] theorem bit_two : (2 : Bit) = 0 := rfl

@[simp] theorem bit_self (a : Bit) : a + a = 0 := by
  simpa only [ZMod.neg_eq_self_mod_two] using add_neg_cancel a

theorem bit_eq (a b : Bit) : a + b = 0 ↔ a = b := by
  rw [← eq_neg_iff_add_eq_zero, ZMod.neg_eq_self_mod_two]

theorem bit_cancel (a b : Bit) : a + b + a = b := by
  rw [add_right_comm, bit_self, zero_add]

theorem bit_cancel_right (a b : Bit) : a + (a + b) = b := by
  rw [← add_assoc, bit_self, zero_add]

def rowSum (f : ℤ → Bit) (lo j : ℤ) : Bit :=
  ∑ t ∈ Finset.range (j - lo + 1).toNat, f (lo + (t : ℤ))

theorem prefix_below (f : ℤ → Bit) (lo j : ℤ) (hj : j < lo) :
    rowSum f lo j = 0 := by
  have hz : (j - lo + 1).toNat = 0 := by omega
  simp [rowSum, hz]

theorem prefix_zero (lo j : ℤ) : rowSum (fun _ => 0) lo j = 0 := by
  simp [rowSum]

theorem prefix_add (f g : ℤ → Bit) (lo j : ℤ) :
    rowSum (fun t => f t + g t) lo j = rowSum f lo j + rowSum g lo j := by
  simp [rowSum, Finset.sum_add_distrib]

theorem prefix_step (f : ℤ → Bit) (lo j : ℤ)
    (hbelow : ∀ t < lo, f t = 0) :
    rowSum f lo j + rowSum f lo (j - 1) = f j := by
  by_cases hj : j < lo
  · rw [prefix_below f lo j hj, prefix_below f lo (j-1) (by omega), hbelow j hj]
    simp
  · have hn : (j - lo + 1).toNat = (j - lo).toNat + 1 := by omega
    have hp : j - 1 - lo + 1 = j - lo := by omega
    have ht : lo + ((j - lo).toNat : ℤ) = j := by omega
    simp only [rowSum, hn, hp, Finset.sum_range_succ, ht]
    exact bit_cancel _ _

theorem prefix_telescope (f : ℤ → Bit) (lo j : ℤ)
    (hlow : f (lo - 1) = 0) (hj : lo ≤ j) :
    rowSum (fun t => f t + f (t - 1)) lo j = f j := by
  have htel : ∀ n : ℕ,
      (∑ t ∈ Finset.range n, (f (lo + (t : ℤ)) + f (lo + (t : ℤ) - 1))) =
        f (lo + (n : ℤ) - 1) := by
    intro n
    induction n with
    | zero => simpa using hlow.symm
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have heq : lo + ((n + 1 : ℕ) : ℤ) - 1 = lo + (n : ℤ) := by omega
      rw [heq]
      simpa only [add_assoc] using bit_cancel (f (lo + (n : ℤ) - 1)) (f (lo + (n : ℤ)))
  unfold rowSum
  rw [htel]
  congr 1
  omega

theorem constant_of_step (f : ℤ → Bit) (hs : ∀ j, f j = f (j - 1)) (a b : ℤ) :
    f a = f b := by
  have hzero : ∀ j : ℤ, f j = f 0 := by
    intro j
    induction j using Int.induction_on with
    | zero => rfl
    | succ j ih =>
      have h : f ((j : ℤ) + 1) = f (j : ℤ) := by simpa using hs ((j : ℤ) + 1)
      exact h.trans ih
    | pred j ih =>
      exact (hs (-(j : ℤ))).symm.trans ih
  exact (hzero a).trans (hzero b).symm

theorem local_parity (a b c d e f t : Bit) (h : a + b + c + d + e + f = 0) :
    (b + t) + (a + e) = (d + t) + (c + f) := by
  have hh := congrArg (fun z : Bit => z + (d + t) + (c + f)) h
  ring_nf at hh ⊢
  simpa using hh

theorem parity_unique (a b c d e f : Bit)
    (h1 : a + b = d + e) (h2 : a + c = d + f) : b + e = c + f := by
  have hs := congrArg₂ (fun x y : Bit => x + y) h1 h2
  have hh := congrArg (fun z : Bit => z + c + e) hs
  ring_nf at hh
  simpa using hh

def Outside (N : ℕ) (i j : ℤ) : Prop :=
  i < -(N : ℤ) ∨ (N : ℤ) < i ∨ j < -(N : ℤ) ∨ (N : ℤ) < j

/-- Each undirected contact has one canonical index:
horizontal (i,j)--(i+1,j), vertical (i,j)--(i,j+1), and
diagonal (i+1,j)--(i,j+1). A nonzero parity bit selects it. -/
structure Edges where
  horizontal : ℤ → ℤ → Bit
  vertical : ℤ → ℤ → Bit
  diagonal : ℤ → ℤ → Bit

theorem Edges.ext {E F : Edges}
    (hh : E.horizontal = F.horizontal) (hv : E.vertical = F.vertical)
    (hk : E.diagonal = F.diagonal) : E = F := by
  cases E
  cases F
  cases hh
  cases hv
  cases hk
  rfl

def Edges.Bounded (E : Edges) (N : ℕ) : Prop :=
  ∀ i j, Outside N i j →
    E.horizontal i j = 0 ∧ E.vertical i j = 0 ∧ E.diagonal i j = 0

def Edges.Finite (E : Edges) : Prop := ∃ N, E.Bounded N

def Edges.Even (E : Edges) : Prop :=
  ∀ i j, E.horizontal (i-1) j + E.horizontal i j +
    E.vertical i (j-1) + E.vertical i j +
    E.diagonal (i-1) j + E.diagonal i (j-1) = 0

structure Filling where
  up : ℤ → ℤ → Bit
  down : ℤ → ℤ → Bit

def Filling.Bounded (R : Filling) (N : ℕ) : Prop :=
  ∀ i j, Outside N i j → R.up i j = 0 ∧ R.down i j = 0

def Filling.Finite (R : Filling) : Prop := ∃ N, R.Bounded N

def Filling.boundary (R : Filling) : Edges where
  horizontal i j := R.up i j + R.down i (j-1)
  vertical i j := R.up i j + R.down (i-1) j
  diagonal i j := R.up i j + R.down i j

theorem boundary_horizontal_iff (R : Filling) (i j : ℤ) :
    R.boundary.horizontal i j ≠ 0 ↔ R.up i j ≠ R.down i (j-1) :=
  not_congr (bit_eq _ _)

theorem boundary_vertical_iff (R : Filling) (i j : ℤ) :
    R.boundary.vertical i j ≠ 0 ↔ R.up i j ≠ R.down (i-1) j :=
  not_congr (bit_eq _ _)

theorem boundary_diagonal_iff (R : Filling) (i j : ℤ) :
    R.boundary.diagonal i j ≠ 0 ↔ R.up i j ≠ R.down i j :=
  not_congr (bit_eq _ _)

def Edges.A (E : Edges) (i j : ℤ) : Bit := E.horizontal i j + E.diagonal i j
def Edges.B (E : Edges) (i j : ℤ) : Bit := E.vertical i j + E.diagonal i j

theorem Edges.local_identity (E : Edges) (he : E.Even) (i j : ℤ) :
    E.A i j + E.A (i-1) j = E.B i j + E.B i (j-1) :=
  local_parity _ _ _ _ _ _ _ (he i j)

def beta (E : Edges) (N : ℕ) (i j : ℤ) : Bit :=
  rowSum (E.A i) (-(N : ℤ)) j

def fill (E : Edges) (N : ℕ) : Filling where
  down := beta E N
  up i j := E.diagonal i j + beta E N i j

theorem beta_step (E : Edges) (N : ℕ) (hb : E.Bounded N) (i j : ℤ) :
    beta E N i j + beta E N i (j-1) = E.A i j := by
  apply prefix_step
  intro t ht
  have hz := hb i t (Or.inr (Or.inr (Or.inl ht)))
  simp [Edges.A, hz.1, hz.2.2]

theorem beta_side (E : Edges) (N : ℕ) (hb : E.Bounded N) (he : E.Even) (i j : ℤ) :
    beta E N i j + beta E N (i-1) j = E.B i j := by
  by_cases hj : j < -(N : ℤ)
  · have hz := hb i j (Or.inr (Or.inr (Or.inl hj)))
    simp [beta, prefix_below _ _ _ hj, Edges.B, hz.2.1, hz.2.2]
  · change rowSum (E.A i) (-(N : ℤ)) j +
      rowSum (E.A (i-1)) (-(N : ℤ)) j = E.B i j
    rw [← prefix_add]
    have hf : (fun t => E.A i t + E.A (i-1) t) =
        (fun t => E.B i t + E.B i (t-1)) := by
      funext t
      exact E.local_identity he i t
    rw [hf]
    apply prefix_telescope
    · have hz := hb i (-(N : ℤ)-1) (Or.inr (Or.inr (Or.inl (by omega))))
      simp [Edges.B, hz.2.1, hz.2.2]
    · omega

theorem fill_boundary (E : Edges) (N : ℕ) (hb : E.Bounded N) (he : E.Even) :
    (fill E N).boundary = E := by
  have hh : (fill E N).boundary.horizontal = E.horizontal := by
    funext i j
    change (E.diagonal i j + beta E N i j) + beta E N i (j-1) = E.horizontal i j
    rw [add_assoc, beta_step E N hb, Edges.A]
    simpa only [add_assoc] using bit_cancel (E.diagonal i j) (E.horizontal i j)
  have hv : (fill E N).boundary.vertical = E.vertical := by
    funext i j
    change (E.diagonal i j + beta E N i j) + beta E N (i-1) j = E.vertical i j
    rw [add_assoc, beta_side E N hb he, Edges.B]
    simpa only [add_assoc] using bit_cancel (E.diagonal i j) (E.vertical i j)
  have hk : (fill E N).boundary.diagonal = E.diagonal := by
    funext i j
    change (E.diagonal i j + beta E N i j) + beta E N i j = E.diagonal i j
    rw [add_assoc, bit_self, add_zero]
  exact Edges.ext hh hv hk

theorem beta_column_zero (E : Edges) (N : ℕ) (hb : E.Bounded N)
    (i j : ℤ) (hi : i < -(N : ℤ) ∨ (N : ℤ) < i) : beta E N i j = 0 := by
  unfold beta rowSum
  apply Finset.sum_eq_zero
  intro t _
  have hout : Outside N i (-(N : ℤ) + (t : ℤ)) := by
    rcases hi with hi | hi
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
  have hz := hb _ _ hout
  simp [Edges.A, hz.1, hz.2.2]

theorem beta_bounded (E : Edges) (N : ℕ) (hb : E.Bounded N) (he : E.Even)
    (i j : ℤ) (hout : Outside N i j) : beta E N i j = 0 := by
  rcases hout with hi | hi | hj | hj
  · exact beta_column_zero E N hb i j (Or.inl hi)
  · exact beta_column_zero E N hb i j (Or.inr hi)
  · exact prefix_below _ _ _ hj
  · have hs : ∀ t, beta E N t j = beta E N (t-1) j := by
      intro t
      apply (bit_eq _ _).mp
      rw [beta_side E N hb he]
      have hz := hb t j (Or.inr (Or.inr (Or.inr hj)))
      simp [Edges.B, hz.2.1, hz.2.2]
    calc
      beta E N i j = beta E N ((N : ℤ)+1) j :=
        constant_of_step (fun t => beta E N t j) hs i _
      _ = 0 := beta_column_zero E N hb _ j (Or.inr (by omega))

theorem fill_bounded (E : Edges) (N : ℕ) (hb : E.Bounded N) (he : E.Even) :
    (fill E N).Bounded N := by
  intro i j hout
  have hbeta := beta_bounded E N hb he i j hout
  have hk := (hb i j hout).2.2
  constructor
  · change E.diagonal i j + beta E N i j = 0
    rw [hk, hbeta, add_zero]
  · exact hbeta

theorem Filling.ext {R S : Filling} (hu : R.up = S.up) (hd : R.down = S.down) :
    R = S := by
  cases R
  cases S
  cases hu
  cases hd
  rfl

theorem filling_unique (R S : Filling) (hR : R.Finite) (hS : S.Finite)
    (heq : R.boundary = S.boundary) : R = S := by
  obtain ⟨N, hN⟩ := hR
  obtain ⟨M, hM⟩ := hS
  have hd : ∀ i j, R.down i j = S.down i j := by
    intro i j
    have hs : ∀ t, R.down i t + S.down i t =
        R.down i (t-1) + S.down i (t-1) := by
      intro t
      have hk := congrArg (fun E : Edges => E.diagonal i t) heq
      have hh := congrArg (fun E : Edges => E.horizontal i t) heq
      exact parity_unique _ _ _ _ _ _ hk hh
    apply (bit_eq _ _).mp
    have hn : Outside N i (-(N : ℤ)-(M : ℤ)-1) := by
      unfold Outside
      omega
    have hm : Outside M i (-(N : ℤ)-(M : ℤ)-1) := by
      unfold Outside
      omega
    rw [constant_of_step (fun t => R.down i t + S.down i t) hs j
      (-(N : ℤ)-(M : ℤ)-1), (hN _ _ hn).2, (hM _ _ hm).2, add_zero]
  have hu : R.up = S.up := by
    funext i j
    have hk := congrArg (fun E : Edges => E.diagonal i j) heq
    change R.up i j + R.down i j = S.up i j + S.down i j at hk
    rw [hd i j] at hk
    exact add_right_cancel hk
  exact Filling.ext hu (funext fun i => funext fun j => hd i j)

theorem finite_filling (E : Edges) (hf : E.Finite) (he : E.Even) :
    ∃! R : Filling, R.Finite ∧ R.boundary = E := by
  obtain ⟨N, hN⟩ := hf
  refine ⟨fill E N, ⟨⟨N, fill_bounded E N hN he⟩, fill_boundary E N hN he⟩, ?_⟩
  intro S hS
  exact filling_unique S (fill E N) hS.1 ⟨N, fill_bounded E N hN he⟩
    (hS.2.trans (fill_boundary E N hN he).symm)

theorem boundary_even (R : Filling) : R.boundary.Even := by
  intro i j
  dsimp [Filling.boundary]
  ring_nf
  simp

theorem boundary_finite (R : Filling) (hf : R.Finite) : R.boundary.Finite := by
  obtain ⟨N, hN⟩ := hf
  refine ⟨N+1, ?_⟩
  intro i j hout
  have h0 : Outside N i j := by unfold Outside at *; omega
  have hi : Outside N (i-1) j := by unfold Outside at *; omega
  have hj : Outside N i (j-1) := by unfold Outside at *; omega
  have hz := hN i j h0
  have hzi := hN (i-1) j hi
  have hzj := hN i (j-1) hj
  simp [Filling.boundary, hz.1, hz.2, hzi.2, hzj.2]

/-- Six side-neighbour positions for hexagonal tile centres. -/
def Adj (p q : Vertex) : Prop :=
  q = (p.1+1, p.2) ∨ q = (p.1, p.2+1) ∨ q = (p.1-1, p.2+1) ∨
  q = (p.1-1, p.2) ∨ q = (p.1, p.2-1) ∨ q = (p.1+1, p.2-1)

theorem adj_symmetric (p q : Vertex) (h : Adj p q) : Adj q p := by
  rcases p with ⟨i,j⟩
  rcases q with ⟨k,l⟩
  simp only [Adj, Prod.mk.injEq] at *
  omega

theorem adj_irrefl (p : Vertex) : ¬ Adj p p := by
  rcases p with ⟨i,j⟩
  simp only [Adj, Prod.mk.injEq]
  omega

abbrev Support := Finset Vertex

/-- The full induced contact relation, not a chosen subset of contacts. -/
def Contact (S : Support) (p q : Vertex) : Prop := p ∈ S ∧ q ∈ S ∧ Adj p q

theorem contact_symmetric (S : Support) (p q : Vertex) (h : Contact S p q) :
    Contact S q p := ⟨h.2.1, h.1, adj_symmetric p q h.2.2⟩

theorem contact_irrefl (S : Support) (p : Vertex) : ¬ Contact S p p :=
  fun h => adj_irrefl p h.2.2

def upVertices (i j : ℤ) : Finset Vertex := {(i,j), (i+1,j), (i,j+1)}
def downVertices (i j : ℤ) : Finset Vertex := {(i+1,j), (i+1,j+1), (i,j+1)}

theorem up_triangle_adj (i j : ℤ) (p q : Vertex)
    (hp : p ∈ upVertices i j) (hq : q ∈ upVertices i j) (hne : p ≠ q) :
    Adj p q := by
  simp only [upVertices, Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    simp_all [Adj]

theorem down_triangle_adj (i j : ℤ) (p q : Vertex)
    (hp : p ∈ downVertices i j) (hq : q ∈ downVertices i j) (hne : p ≠ q) :
    Adj p q := by
  simp only [downVertices, Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    simp_all [Adj]

/-- A selected contact has both endpoints in the support. -/
def Edges.Supported (E : Edges) (S : Support) : Prop :=
  (∀ i j, (i,j) ∉ S ∨ (i+1,j) ∉ S → E.horizontal i j = 0) ∧
  (∀ i j, (i,j) ∉ S ∨ (i,j+1) ∉ S → E.vertical i j = 0) ∧
  (∀ i j, (i+1,j) ∉ S ∨ (i,j+1) ∉ S → E.diagonal i j = 0)

/-- A finite walk through unoccupied lattice vertices. -/
inductive EmptyPath (S : Support) : Vertex → Vertex → Prop
  | refl (p : Vertex) (hp : p ∉ S) : EmptyPath S p p
  | step {p q r : Vertex} (path : EmptyPath S p q) (adj : Adj q r)
      (hr : r ∉ S) : EmptyPath S p r

theorem EmptyPath.end_empty {S : Support} {p q : Vertex} (path : EmptyPath S p q) :
    q ∉ S := by
  cases path with
  | refl hp => exact hp
  | step _ _ hr => exact hr

/-- Every unoccupied cell can escape every finite centred coordinate box
through unoccupied side-neighbours. No filling or area property is assumed. -/
def NoHoles (S : Support) : Prop :=
  ∀ p, p ∉ S → ∀ N : ℕ, ∃ q, EmptyPath S p q ∧ Outside N q.1 q.2

def Filling.Contained (R : Filling) (S : Support) : Prop :=
  ∀ i j, (R.up i j ≠ 0 → upVertices i j ⊆ S) ∧
    (R.down i j ≠ 0 → downVertices i j ⊆ S)

/-- The five other triangles at an empty vertex have the same label as
the upward triangle anchored there. -/
theorem empty_incident (R : Filling) (S : Support) (hs : R.boundary.Supported S)
    (i j : ℤ) (hp : (i,j) ∉ S) :
    R.up (i-1) j = R.up i j ∧ R.up i (j-1) = R.up i j ∧
    R.down (i-1) j = R.up i j ∧ R.down i (j-1) = R.up i j ∧
    R.down (i-1) (j-1) = R.up i j := by
  have hv := hs.2.1 i j (Or.inl hp)
  have hh := hs.1 i j (Or.inl hp)
  have hk0 := hs.2.2 (i-1) j (Or.inl (by simpa using hp))
  have hk1 := hs.2.2 i (j-1) (Or.inr (by simpa using hp))
  have hh0 := hs.1 (i-1) j (Or.inr (by simpa using hp))
  have hd0 : R.down (i-1) j = R.up i j := (bit_eq _ _).mp hv |>.symm
  have hd1 : R.down i (j-1) = R.up i j := (bit_eq _ _).mp hh |>.symm
  have hu0 : R.up (i-1) j = R.up i j := ((bit_eq _ _).mp hk0).trans hd0
  have hu1 : R.up i (j-1) = R.up i j := ((bit_eq _ _).mp hk1).trans hd1
  have hd2 : R.down (i-1) (j-1) = R.up i j :=
    ((bit_eq _ _).mp hh0).symm.trans hu0
  exact ⟨hu0, hu1, hd0, hd1, hd2⟩

theorem empty_adjacent_label (R : Filling) (S : Support)
    (hs : R.boundary.Supported S) (p q : Vertex)
    (hp : p ∉ S) (hq : q ∉ S) (hadj : Adj p q) :
    R.up p.1 p.2 = R.up q.1 q.2 := by
  rcases p with ⟨i,j⟩
  rcases hadj with h | h | h | h | h | h <;> subst q
  · simpa using (empty_incident R S hs (i+1) j hq).1
  · simpa using (empty_incident R S hs i (j+1) hq).2.1
  · have h0 := (empty_incident R S hs i j hp).1
    have h1 := (empty_incident R S hs (i-1) (j+1) hq).2.1
    exact h0.symm.trans (by simpa using h1)
  · exact (empty_incident R S hs i j hp).1.symm
  · exact (empty_incident R S hs i j hp).2.1.symm
  · have h0 := (empty_incident R S hs i j hp).2.1
    have h1 := (empty_incident R S hs (i+1) (j-1) hq).1
    exact h0.symm.trans (by simpa using h1)

theorem empty_path_label (R : Filling) (S : Support)
    (hs : R.boundary.Supported S) {p q : Vertex} (path : EmptyPath S p q) :
    R.up p.1 p.2 = R.up q.1 q.2 := by
  induction path with
  | refl _ => rfl
  | step path adj hr ih =>
    exact ih.trans (empty_adjacent_label R S hs _ _ path.end_empty hr adj)

theorem empty_up_zero (R : Filling) (S : Support) (hf : R.Finite)
    (hs : R.boundary.Supported S) (hn : NoHoles S) (i j : ℤ) (hp : (i,j) ∉ S) :
    R.up i j = 0 := by
  obtain ⟨N, hN⟩ := hf
  obtain ⟨q, path, hq⟩ := hn (i,j) hp N
  exact (empty_path_label R S hs path).trans (hN q.1 q.2 hq).1

theorem filling_contained (R : Filling) (S : Support) (hf : R.Finite)
    (hs : R.boundary.Supported S) (hn : NoHoles S) : R.Contained S := by
  intro i j
  constructor
  · intro hu
    have h0 : (i,j) ∈ S := by
      by_contra hp
      exact hu (empty_up_zero R S hf hs hn i j hp)
    have h1 : (i+1,j) ∈ S := by
      by_contra hp
      have he := (empty_incident R S hs (i+1) j hp).1
      have hz := empty_up_zero R S hf hs hn (i+1) j hp
      exact hu (by simpa using he.trans hz)
    have h2 : (i,j+1) ∈ S := by
      by_contra hp
      have he := (empty_incident R S hs i (j+1) hp).2.1
      have hz := empty_up_zero R S hf hs hn i (j+1) hp
      exact hu (by simpa using he.trans hz)
    simpa only [upVertices, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      using And.intro h0 (And.intro h1 h2)
  · intro hd
    have h0 : (i+1,j) ∈ S := by
      by_contra hp
      have he := (empty_incident R S hs (i+1) j hp).2.2.1
      have hz := empty_up_zero R S hf hs hn (i+1) j hp
      exact hd (by simpa using he.trans hz)
    have h1 : (i+1,j+1) ∈ S := by
      by_contra hp
      have he := (empty_incident R S hs (i+1) (j+1) hp).2.2.2.2
      have hz := empty_up_zero R S hf hs hn (i+1) (j+1) hp
      exact hd (by simpa using he.trans hz)
    have h2 : (i,j+1) ∈ S := by
      by_contra hp
      have he := (empty_incident R S hs i (j+1) hp).2.2.2.1
      have hz := empty_up_zero R S hf hs hn i (j+1) hp
      exact hd (by simpa using he.trans hz)
    simpa only [downVertices, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      using And.intro h0 (And.intro h1 h2)

theorem finite_filling_inside (E : Edges) (S : Support) (hf : E.Finite)
    (he : E.Even) (hs : E.Supported S) (hn : NoHoles S) :
    ∃! R : Filling, R.Finite ∧ R.boundary = E ∧ R.Contained S := by
  obtain ⟨R, ⟨hR, hb⟩, huniq⟩ := finite_filling E hf he
  have hinside := filling_contained R S hR (by rwa [hb]) hn
  refine ⟨R, ⟨hR, hb, hinside⟩, ?_⟩
  intro T hT
  exact huniq T ⟨hT.1, hT.2.1⟩

def supportRadius (S : Support) : ℕ :=
  S.sup (fun p => p.1.natAbs + p.2.natAbs)

theorem support_in_box (S : Support) (i j : ℤ) (hp : (i,j) ∈ S) :
    ¬ Outside (supportRadius S) i j := by
  have hsup : i.natAbs + j.natAbs ≤ supportRadius S :=
    Finset.le_sup (f := fun p : Vertex => p.1.natAbs + p.2.natAbs) hp
  have hi : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
  have hni : -i ≤ (i.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -i))
  have hj : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
  have hnj : -j ≤ (j.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -j))
  unfold Outside
  omega

theorem supported_finite (E : Edges) (S : Support) (hs : E.Supported S) : E.Finite := by
  refine ⟨supportRadius S + 1, ?_⟩
  intro i j hout
  have hp : (i,j) ∉ S := by
    intro hmem
    have hi := support_in_box S i j hmem
    unfold Outside at *
    omega
  have hp' : (i+1,j) ∉ S := by
    intro hmem
    have hi := support_in_box S (i+1) j hmem
    unfold Outside at *
    omega
  exact ⟨hs.1 i j (Or.inl hp), hs.2.1 i j (Or.inl hp), hs.2.2 i j (Or.inl hp')⟩

/-- Every even edge subset of a finite hole-free support has a unique
finite filling, and every filled triangle has all three vertices occupied. -/
theorem support_filling (E : Edges) (S : Support)
    (he : E.Even) (hs : E.Supported S) (hn : NoHoles S) :
    ∃! R : Filling, R.Finite ∧ R.boundary = E ∧ R.Contained S :=
  finite_filling_inside E S (supported_finite E S hs) he hs hn

/-- Coordinate boundedness is exactly ordinary finite support, not a
stronger restriction on admissible patterns. -/
theorem finite_support_iff (f : ℤ → ℤ → Bit) :
    (∃ N : ℕ, ∀ i j, Outside N i j → f i j = 0) ↔
      Set.Finite {p : Vertex | f p.1 p.2 ≠ 0} := by
  classical
  constructor
  · rintro ⟨N, hN⟩
    refine (Finset.finite_toSet
      ((Finset.Icc (-(N : ℤ)) (N : ℤ)).product
        (Finset.Icc (-(N : ℤ)) (N : ℤ)))).subset ?_
    intro p hp
    have hn : ¬ Outside N p.1 p.2 := by
      intro ho
      exact hp (hN p.1 p.2 ho)
    change p ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).product
      (Finset.Icc (-(N : ℤ)) (N : ℤ))
    rw [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    unfold Outside at hn
    omega
  · intro hf
    refine ⟨supportRadius hf.toFinset, ?_⟩
    intro i j hout
    by_contra hn
    have hm : (i,j) ∈ hf.toFinset := hf.mem_toFinset.mpr hn
    exact support_in_box hf.toFinset i j hm hout

theorem filling_finite_iff (R : Filling) :
    R.Finite ↔
      Set.Finite {p : Vertex | R.up p.1 p.2 ≠ 0} ∧
      Set.Finite {p : Vertex | R.down p.1 p.2 ≠ 0} := by
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨(finite_support_iff R.up).mp ⟨N, fun i j h => (hN i j h).1⟩,
      (finite_support_iff R.down).mp ⟨N, fun i j h => (hN i j h).2⟩⟩
  · rintro ⟨hu, hd⟩
    obtain ⟨N, hN⟩ := (finite_support_iff R.up).mpr hu
    obtain ⟨M, hM⟩ := (finite_support_iff R.down).mpr hd
    refine ⟨N+M, ?_⟩
    intro i j hout
    constructor
    · apply hN
      unfold Outside at *
      omega
    · apply hM
      unfold Outside at *
      omega

theorem edges_finite_iff (E : Edges) :
    E.Finite ↔
      Set.Finite {p : Vertex | E.horizontal p.1 p.2 ≠ 0} ∧
      Set.Finite {p : Vertex | E.vertical p.1 p.2 ≠ 0} ∧
      Set.Finite {p : Vertex | E.diagonal p.1 p.2 ≠ 0} := by
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨(finite_support_iff E.horizontal).mp ⟨N, fun i j h => (hN i j h).1⟩,
      (finite_support_iff E.vertical).mp ⟨N, fun i j h => (hN i j h).2.1⟩,
      (finite_support_iff E.diagonal).mp ⟨N, fun i j h => (hN i j h).2.2⟩⟩
  · rintro ⟨hh, hv, hk⟩
    obtain ⟨N, hN⟩ := (finite_support_iff E.horizontal).mpr hh
    obtain ⟨M, hM⟩ := (finite_support_iff E.vertical).mpr hv
    obtain ⟨K, hK⟩ := (finite_support_iff E.diagonal).mpr hk
    refine ⟨N+M+K, ?_⟩
    intro i j hout
    refine ⟨hN i j ?_, hM i j ?_, hK i j ?_⟩ <;>
      unfold Outside at * <;> omega

theorem up_zero_of_missing (R : Filling) (S : Support) (hc : R.Contained S)
    (i j : ℤ) (p : Vertex) (hp : p ∈ upVertices i j) (hn : p ∉ S) :
    R.up i j = 0 := by
  by_contra h
  exact hn ((hc i j).1 h hp)

theorem down_zero_of_missing (R : Filling) (S : Support) (hc : R.Contained S)
    (i j : ℤ) (p : Vertex) (hp : p ∈ downVertices i j) (hn : p ∉ S) :
    R.down i j = 0 := by
  by_contra h
  exact hn ((hc i j).2 h hp)

theorem boundary_supported (R : Filling) (S : Support) (hc : R.Contained S) :
    R.boundary.Supported S := by
  constructor
  · intro i j hm
    have hu : R.up i j = 0 := by
      rcases hm with h | h
      · exact up_zero_of_missing R S hc i j (i,j) (by simp [upVertices]) h
      · exact up_zero_of_missing R S hc i j (i+1,j) (by simp [upVertices]) h
    have hd : R.down i (j-1) = 0 := by
      rcases hm with h | h
      · exact down_zero_of_missing R S hc i (j-1) (i,j) (by simp [downVertices]) h
      · exact down_zero_of_missing R S hc i (j-1) (i+1,j) (by simp [downVertices]) h
    change R.up i j + R.down i (j-1) = 0
    rw [hu, hd, add_zero]
  constructor
  · intro i j hm
    have hu : R.up i j = 0 := by
      rcases hm with h | h
      · exact up_zero_of_missing R S hc i j (i,j) (by simp [upVertices]) h
      · exact up_zero_of_missing R S hc i j (i,j+1) (by simp [upVertices]) h
    have hd : R.down (i-1) j = 0 := by
      rcases hm with h | h
      · exact down_zero_of_missing R S hc (i-1) j (i,j) (by simp [downVertices]) h
      · exact down_zero_of_missing R S hc (i-1) j (i,j+1) (by simp [downVertices]) h
    change R.up i j + R.down (i-1) j = 0
    rw [hu, hd, add_zero]
  · intro i j hm
    have hu : R.up i j = 0 := by
      rcases hm with h | h
      · exact up_zero_of_missing R S hc i j (i+1,j) (by simp [upVertices]) h
      · exact up_zero_of_missing R S hc i j (i,j+1) (by simp [upVertices]) h
    have hd : R.down i j = 0 := by
      rcases hm with h | h
      · exact down_zero_of_missing R S hc i j (i+1,j) (by simp [downVertices]) h
      · exact down_zero_of_missing R S hc i j (i,j+1) (by simp [downVertices]) h
    change R.up i j + R.down i j = 0
    rw [hu, hd, add_zero]

/-- Containment in a finite support already guarantees finiteness. -/
theorem contained_finite (R : Filling) (S : Support) (hc : R.Contained S) : R.Finite := by
  refine ⟨supportRadius S + 1, ?_⟩
  intro i j hout
  have hp : (i,j) ∉ S := by
    intro hm
    have hi := support_in_box S i j hm
    unfold Outside at *
    omega
  have hq : (i+1,j) ∉ S := by
    intro hm
    have hi := support_in_box S (i+1) j hm
    unfold Outside at *
    omega
  exact ⟨up_zero_of_missing R S hc i j (i,j) (by simp [upVertices]) hp,
    down_zero_of_missing R S hc i j (i+1,j) (by simp [downVertices]) hq⟩

abbrev InsideFillings (S : Support) := {R : Filling // R.Contained S}
abbrev EvenNetworks (S : Support) := {E : Edges // E.Even ∧ E.Supported S}

def boundaryMap (S : Support) (R : InsideFillings S) : EvenNetworks S :=
  ⟨R.val.boundary, boundary_even R.val, boundary_supported R.val S R.property⟩

/-- The triangle-filling bijection, for finite supports with the stated
empty-cell escape condition. No graph-counting or area theorem is assumed. -/
theorem boundary_bijective (S : Support) (hn : NoHoles S) :
    Function.Bijective (boundaryMap S) := by
  constructor
  · intro R T h
    apply Subtype.ext
    have hb := congrArg Subtype.val h
    exact filling_unique R.val T.val (contained_finite R.val S R.property)
      (contained_finite T.val S T.property) hb
  · intro E
    obtain ⟨R, ⟨_, hb, hi⟩, _⟩ := support_filling E.val S E.property.1 E.property.2 hn
    refine ⟨⟨R, hi⟩, ?_⟩
    exact Subtype.ext hb

end Tantrix.Grid
