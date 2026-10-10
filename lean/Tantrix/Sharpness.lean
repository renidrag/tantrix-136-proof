import Tantrix.GeometryApplication
import Tantrix.GridExamples

/-!
# The concrete 136-edge witness

The 55-cell triangle i,j ≥ 0, i+j ≤ 9, with the extra cell (5,-1).
Removing the contact (4,0)--(5,0) leaves an even network with 136 edges.
This certifies geometric sharpness, not a coloured Tantrix placement.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Tantrix.Grid.Witness136

def support : Support :=
  insert (5,-1)
    (((Finset.Icc (0 : ℤ) 9).product (Finset.Icc (0 : ℤ) 9)).filter
      (fun p => p.1+p.2 ≤ 9))

@[simp] theorem mem_support (i j : ℤ) :
    (i,j) ∈ support ↔ (i = 5 ∧ j = -1) ∨ (0 ≤ i ∧ 0 ≤ j ∧ i+j ≤ 9) := by
  simp only [support, Finset.mem_insert, Finset.mem_filter, Prod.mk.injEq]
  simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  omega

theorem card_support : support.card = 56 := by decide

/-- Every empty cell has a clear horizontal ray to infinity. -/
theorem no_holes : NoHoles support := by
  intro p hp N
  rcases p with ⟨i,j⟩
  by_cases hr : (j = -1 ∧ 5 < i) ∨ (j ≠ -1 ∧ (j < 0 ∨ 9 < i+j))
  · have hclear : ∀ n : ℕ, (i+(n : ℤ),j) ∉ support := by
      intro n
      simp only [mem_support]
      omega
    refine ⟨(i+((N+i.natAbs+1 : ℕ) : ℤ),j), clear_east_path _ i j hclear _, ?_⟩
    apply Or.inr
    apply Or.inl
    have ha : -i ≤ (i.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -i))
    dsimp
    omega
  · have hclear : ∀ n : ℕ, (i-(n : ℤ),j) ∉ support := by
      intro n
      simp only [mem_support] at hp ⊢
      omega
    refine ⟨(i-((N+i.natAbs+1 : ℕ) : ℤ),j), clear_west_path _ i j hclear _, ?_⟩
    apply Or.inl
    have ha : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
    dsimp
    omega

theorem connected : Connected support := by
  let origin : Cells support := ⟨(0,0),by decide⟩
  let cell (i j : ℕ) (h : i+j ≤ 9) : Cells support :=
    ⟨((i : ℤ),(j : ℤ)), mem_support _ _ |>.mpr (Or.inr (by omega))⟩
  have reach : ∀ i j : ℕ, ∀ h : i+j ≤ 9,
      Relation.ReflTransGen (FiniteGraph.Adj (firstCell support) (lastCell support))
        origin (cell i j h) := by
    intro i
    induction i with
    | zero =>
      intro j
      induction j with
      | zero => intro h; exact Relation.ReflTransGen.refl
      | succ j ih =>
        intro h
        apply Relation.ReflTransGen.tail (ih (by omega))
        apply (indexed_adjacency_iff _ _ _).mpr
        exact Or.inr (Or.inl (by simp [cell, Nat.cast_add]))
    | succ i ih =>
      intro j h
      apply Relation.ReflTransGen.tail (ih j (by omega))
      apply (indexed_adjacency_iff _ _ _).mpr
      exact Or.inl (by simp [cell, Nat.cast_add])
  have all_reach (p : Cells support) :
      Relation.ReflTransGen (FiniteGraph.Adj (firstCell support) (lastCell support))
        origin p := by
    rcases p with ⟨⟨i,j⟩,hp⟩
    rcases (mem_support i j).mp hp with ⟨rfl,rfl⟩ | ⟨hi,hj,hs⟩
    · apply Relation.ReflTransGen.tail (reach 5 0 (by decide))
      exact (indexed_adjacency_iff _ _ _).mpr (by simp [Adj,cell])
    · have hsum : i.toNat+j.toNat ≤ 9 := by omega
      have heq : cell i.toNat j.toNat hsum = (⟨(i,j),hp⟩ : Cells support) := by
        apply Subtype.ext
        simp [cell, Int.toNat_of_nonneg hi, Int.toNat_of_nonneg hj]
      rw [← heq]
      exact reach _ _ hsum
  refine ⟨⟨origin⟩,fun p q => ?_⟩
  let : Std.Symm (FiniteGraph.Adj (firstCell support) (lastCell support)) :=
    ⟨fun a b h => (indexed_adjacency_iff _ _ _).mpr
      (adj_symmetric _ _ ((indexed_adjacency_iff _ a b).mp h))⟩
  exact (Std.Symm.symm _ _ (all_reach p)).trans (all_reach q)

/-- The 135 triangle contacts and the two contacts of the extra cell. -/
def contactIndices : Finset EdgeIndex :=
  {(1,5,-1),(2,4,-1)} ∪
    (Finset.univ ×ˢ (((Finset.Icc (0 : ℤ) 8) ×ˢ (Finset.Icc (0 : ℤ) 8)).filter
      (fun p => p.1+p.2 ≤ 8)))

theorem mem_contactIndices (e : EdgeIndex) :
    e ∈ contactIndices ↔ edgePresent support e := by
  rcases e with ⟨d,i,j⟩
  fin_cases d <;>
    simp [contactIndices, edgePresent, edgeFirst, edgeLast, mem_support, Prod.mk.injEq] <;>
    omega

/-- All contacts except (4,0)--(5,0) are selected. -/
def selected (e : EdgeIndex) : Bit := if e = (0,4,0) then 0 else 1

def network (e : Contacts support) : Bit := selected e.val

set_option maxRecDepth 4096 in
theorem edge_count : edgeCount support = 137 := by
  have h : (∑ _ : Contacts support, (1 : ℕ)) = 137 := by
    rw [← Finset.sum_subtype contactIndices mem_contactIndices (fun _ => (1 : ℕ))]
    decide
  simpa [edgeCount] using h

set_option maxRecDepth 4096 in
theorem selected_count : selectedCount support network = 136 := by
  unfold selectedCount network
  rw [← Finset.sum_subtype contactIndices mem_contactIndices
    (fun e => if selected e = 0 then (0 : ℕ) else 1)]
  decide

/-- All 45 upward triangles, and the downward triangle at the extra cell. -/
def filling : Filling where
  up i j := if 0 ≤ i ∧ 0 ≤ j ∧ i+j ≤ 8 then 1 else 0
  down i j := if i = 4 ∧ j = -1 then 1 else 0

theorem network_boundary : decodeEdges support network = filling.boundary := by
  apply Edges.ext <;> funext i j
  all_goals
    simp [decodeEdges, extend, network, selected, edgePresent, edgeFirst, edgeLast,
      Filling.boundary, filling, Prod.mk.injEq]
    split_ifs <;> norm_num at * <;> first | rfl | omega

theorem even : (decodeEdges support network).Even := by
  rw [network_boundary]
  exact boundary_even filling

/-- This particular support and network attain the already-proved upper bound. -/
theorem maximum : IsMaximum support network := by
  refine ⟨even, fun x hx => ?_⟩
  rw [selected_count]
  exact score_le_136 support connected no_holes card_support x hx

end Tantrix.Grid.Witness136

namespace Tantrix.Grid

/-- A genuine connected, hole-free 56-cell support attains 136.
Together with score_le_136, this makes the geometric upper bound exact. -/
theorem exists_score_136 : ∃ (S : Support) (x : Contacts S → Bit),
    Connected S ∧ NoHoles S ∧ S.card = 56 ∧
      (decodeEdges S x).Even ∧ selectedCount S x = 136 :=
  ⟨Witness136.support, Witness136.network, Witness136.connected, Witness136.no_holes,
    Witness136.card_support, Witness136.even, Witness136.selected_count⟩

end Tantrix.Grid
