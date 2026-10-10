import Tantrix.Disconnected
import Tantrix.CountingExamples

/-! A genuinely disconnected, hole-free support with two nonempty loops.
Its correction is exactly one; the connected triangle has correction zero. -/

set_option autoImplicit false
open scoped BigOperators
open Classical

namespace Tantrix.Grid.DisconnectedExamples

def support : Support := upVertices 0 0 ∪ upVertices 0 3

@[simp] theorem mem_support (i j : ℤ) :
    (i,j) ∈ support ↔ (i = 0 ∧ (j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4)) ∨
      (i = 1 ∧ (j = 0 ∨ j = 3)) := by
  simp [support,upVertices,Prod.mk.injEq]
  omega

theorem card_support : support.card = 6 := by decide

theorem no_holes : NoHoles support := by
  intro p hp N
  rcases p with ⟨i,j⟩
  by_cases hi : 0 ≤ i
  · have hclear : ∀ n : ℕ, (i+(n : ℤ),j) ∉ support := by
      intro n
      simp only [mem_support] at hp ⊢
      omega
    refine ⟨(i+((N+i.natAbs+1 : ℕ) : ℤ),j), clear_east_path _ i j hclear _, ?_⟩
    apply Or.inr
    apply Or.inl
    have ha : -i ≤ (i.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -i))
    dsimp
    omega
  · have hclear : ∀ n : ℕ, (i-(n : ℤ),j) ∉ support := by
      intro n
      simp only [mem_support]
      omega
    refine ⟨(i-((N+i.natAbs+1 : ℕ) : ℤ),j), clear_west_path _ i j hclear _, ?_⟩
    apply Or.inl
    have ha : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
    dsimp
    omega

theorem not_connected : ¬ Connected support := by
  intro hc
  let p : Cells support := ⟨(0,0),by decide⟩
  let q : Cells support := ⟨(0,3),by decide⟩
  have hpath := hc.2 p q
  have hstay : ∀ v : Cells support,
      Relation.ReflTransGen (FiniteGraph.Adj (firstCell support) (lastCell support)) p v →
        v.val.2 ≤ 1 := by
    intro v path
    induction path with
    | refl => decide
    | @tail v w _ hw ih =>
      have ha := (indexed_adjacency_iff support v w).mp hw
      have hm := (mem_support w.val.1 w.val.2).mp w.property
      rcases ha with h | h | h | h | h | h <;>
        have he := congrArg Prod.snd h <;> dsimp at he <;> omega
  have hf := hstay q hpath
  norm_num [q] at hf

def contactIndices : Finset EdgeIndex := Finset.univ ×ˢ {(0,0),(0,3)}

theorem mem_contactIndices (e : EdgeIndex) :
    e ∈ contactIndices ↔ edgePresent support e := by
  rcases e with ⟨d,i,j⟩
  fin_cases d <;>
    simp [contactIndices,edgePresent,edgeFirst,edgeLast,mem_support,Prod.mk.injEq] <;> omega

def triangleIndices : Finset TriangleIndex := {(false,0,0),(false,0,3)}

theorem mem_triangleIndices (t : TriangleIndex) :
    t ∈ triangleIndices ↔ trianglePresent support t := by
  rcases t with ⟨b,i,j⟩
  cases b <;>
    simp [triangleIndices,trianglePresent,triangleVertices,upVertices,downVertices,
      Finset.insert_subset_iff,Finset.singleton_subset_iff,mem_support,Prod.mk.injEq] <;> omega

theorem counts : edgeCount support = 6 ∧ triangleCount support = 2 ∧
    boundaryCount support = 6 := by
  have he : (∑ _ : Contacts support, (1 : ℕ)) = 6 := by
    rw [← Finset.sum_subtype contactIndices mem_contactIndices (fun _ => (1 : ℕ))]
    decide
  have ht : (∑ _ : Triangles support, (1 : ℕ)) = 2 := by
    rw [← Finset.sum_subtype triangleIndices mem_triangleIndices (fun _ => (1 : ℕ))]
    decide
  have he' : edgeCount support = 6 := by simpa [edgeCount] using he
  have ht' : triangleCount support = 2 := by simpa [triangleCount] using ht
  have hb : boundaryCount support = 6 := by
    have h1 := contact_partition support
    have h2 := triangle_partition support
    unfold boundaryCount
    omega
  exact ⟨he',ht',hb⟩

def network : Contacts support → Bit := fun _ => 1

def filling : Filling where
  up i j := if i = 0 ∧ (j = 0 ∨ j = 3) then 1 else 0
  down _ _ := 0

theorem network_boundary : decodeEdges support network = filling.boundary := by
  apply Edges.ext <;> funext i j
  all_goals
    simp [decodeEdges,extend,network,← mem_contactIndices,contactIndices,
      Filling.boundary,filling,Prod.mk.injEq,and_or_left]

theorem even : (decodeEdges support network).Even := by
  rw [network_boundary]
  exact boundary_even filling

theorem score_six : selectedCount support network = 6 := by
  simpa [selectedCount,network,edgeCount] using counts.1

/-- The reduction adds one to the omission budget and two to the boundary
budget, while the two disjoint three-edge loops retain score six. -/
theorem correction_one :
    ∃ b : ℕ, b = 1 ∧
      triangleCount support + (boundaryCount support + 2*b) + 2 = 2*support.card ∧
      (edgeCount support + b) + (boundaryCount support + 2*b) + 3 = 3*support.card := by
  obtain ⟨b,hF,hE⟩ := exists_counting_correction support (by decide) no_holes
  have hf := counts.2.1
  have hL := counts.2.2
  have hn := card_support
  exact ⟨b,by omega,hF,hE⟩

/-- On the existing connected example, the correction is zero. -/
theorem correction_zero :
    ∃ b : ℕ, b = 0 ∧
      triangleCount unitTriangleSupport + (boundaryCount unitTriangleSupport + 2*b) + 2 =
        2*unitTriangleSupport.card := by
  obtain ⟨b,hF,_⟩ := exists_counting_correction unitTriangleSupport (by decide)
    unitTriangle_no_holes
  have hc := unitTriangle_counts
  dsimp only [vertexCount] at hc
  exact ⟨b,by omega,hF⟩

/-- The nonempty hypothesis in the counting reduction cannot be discarded. -/
theorem empty_correction_impossible : ¬ ∃ b : ℕ,
    triangleCount ∅ + (boundaryCount ∅ + 2*b) + 2 = 2*(∅ : Support).card := by
  simp only [Finset.card_empty, Nat.mul_zero]
  omega

end Tantrix.Grid.DisconnectedExamples
