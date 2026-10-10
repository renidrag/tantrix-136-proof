import Tantrix.Grid

set_option autoImplicit false

namespace Tantrix.Grid

theorem empty_east_path (i j : ℤ) (n : ℕ) :
    EmptyPath ∅ (i,j) (i+(n : ℤ),j) := by
  induction n with
  | zero => simpa using EmptyPath.refl (S := ∅) (i,j) (by simp)
  | succ n ih =>
    exact EmptyPath.step ih (Or.inl (by simp [Nat.cast_add, add_assoc])) (by simp)

/-- Positive check: the empty support has escape paths of any required length. -/
theorem empty_has_no_holes : NoHoles ∅ := by
  intro p _ N
  rcases p with ⟨i,j⟩
  refine ⟨(i+((N+i.natAbs+1 : ℕ) : ℤ),j), empty_east_path i j _, ?_⟩
  apply Or.inr
  apply Or.inl
  have hi : -i ≤ (i.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -i))
  dsimp
  omega

theorem clear_east_path (S : Support) (i j : ℤ)
    (hclear : ∀ n : ℕ, (i+(n : ℤ),j) ∉ S) (n : ℕ) :
    EmptyPath S (i,j) (i+(n : ℤ),j) := by
  induction n with
  | zero => simpa using EmptyPath.refl (S := S) (i,j) (by simpa using hclear 0)
  | succ n ih =>
    exact EmptyPath.step ih (Or.inl (by simp [Nat.cast_add, add_assoc])) (hclear (n+1))

theorem clear_west_path (S : Support) (i j : ℤ)
    (hclear : ∀ n : ℕ, (i-(n : ℤ),j) ∉ S) (n : ℕ) :
    EmptyPath S (i,j) (i-(n : ℤ),j) := by
  induction n with
  | zero => simpa using EmptyPath.refl (S := S) (i,j) (by simpa using hclear 0)
  | succ n ih =>
    apply EmptyPath.step ih
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inl
      simp [Nat.cast_add]
      ring
    · exact hclear (n+1)

/-- A nonempty positive check for the independently defined no-holes rule. -/
theorem singleton_has_no_holes : NoHoles {(0,0)} := by
  intro p hp N
  rcases p with ⟨i,j⟩
  by_cases hc : j ≠ 0 ∨ 0 < i
  · have hclear : ∀ n : ℕ, (i+(n : ℤ),j) ∉ ({(0,0)} : Support) := by
      intro n
      simp only [Finset.mem_singleton, Prod.mk.injEq]
      omega
    refine ⟨(i+((N+i.natAbs+1 : ℕ) : ℤ),j), clear_east_path _ i j hclear _, ?_⟩
    apply Or.inr
    apply Or.inl
    have hi : -i ≤ (i.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -i))
    dsimp
    omega
  · have hi : i < 0 := by
      simp only [Finset.mem_singleton, Prod.mk.injEq] at hp
      omega
    have hclear : ∀ n : ℕ, (i-(n : ℤ),j) ∉ ({(0,0)} : Support) := by
      intro n
      simp only [Finset.mem_singleton, Prod.mk.injEq]
      omega
    refine ⟨(i-((N+i.natAbs+1 : ℕ) : ℤ),j), clear_west_path _ i j hclear _, ?_⟩
    apply Or.inl
    have habs : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
    dsimp
    omega

def ringSupport : Support := {(1,0), (0,1), (-1,1), (-1,0), (0,-1), (1,-1)}

theorem ring_neighbour_occupied (p : Vertex) (hp : Adj (0,0) p) :
    p ∈ ringSupport := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ring_path_stays {p q : Vertex} (path : EmptyPath ringSupport p q)
    (hp : p = (0,0)) : q = (0,0) := by
  induction path with
  | refl _ => exact hp
  | step path adj hr ih =>
    have hq := ih
    have ho := ring_neighbour_occupied _ (by simpa [hq] using adj)
    exact (hr ho).elim

/-- Negative check: six occupied neighbours trap the unoccupied centre. -/
theorem ring_has_hole : ¬ NoHoles ringSupport := by
  intro hn
  obtain ⟨q, path, hout⟩ := hn (0,0) (by decide) 0
  have hq := ring_path_stays path rfl
  subst q
  norm_num [Outside] at hout

def unitUp : Filling where
  up i j := if i = 0 ∧ j = 0 then 1 else 0
  down _ _ := 0

theorem unitUp_bounded : unitUp.Bounded 0 := by
  intro i j hout
  constructor
  · by_cases h : i = 0 ∧ j = 0
    · rcases h with ⟨rfl,rfl⟩
      norm_num [Outside] at hout
    · simp [unitUp, h]
  · rfl

/-- An upward elementary triangle has exactly its three expected contacts. -/
theorem unitUp_boundary (i j : ℤ) :
    unitUp.boundary.horizontal i j = (if i = 0 ∧ j = 0 then 1 else 0) ∧
    unitUp.boundary.vertical i j = (if i = 0 ∧ j = 0 then 1 else 0) ∧
    unitUp.boundary.diagonal i j = (if i = 0 ∧ j = 0 then 1 else 0) := by
  simp [unitUp, Filling.boundary]

theorem unitUp_edge_bounded : unitUp.boundary.Bounded 0 := by
  intro i j hout
  have hnot : ¬ (i = 0 ∧ j = 0) := by
    unfold Outside at hout
    omega
  simpa [hnot] using unitUp_boundary i j

theorem unitUp_round_trip : fill unitUp.boundary 0 = unitUp := by
  apply filling_unique _ _ ⟨0, fill_bounded _ 0 unitUp_edge_bounded (boundary_even unitUp)⟩
    ⟨0, unitUp_bounded⟩
  exact fill_boundary _ 0 unitUp_edge_bounded (boundary_even unitUp)

end Tantrix.Grid
