import Tantrix.Counting
import Tantrix.GridExamples

set_option autoImplicit false
open Classical

namespace Tantrix.Grid

def unitTriangleSupport : Support := upVertices 0 0

theorem unitTriangle_no_holes : NoHoles unitTriangleSupport := by
  intro p hp N
  rcases p with ⟨i,j⟩
  by_cases hi : 0 ≤ i
  · have hclear : ∀ n : ℕ, (i+(n : ℤ),j) ∉ unitTriangleSupport := by
      intro n
      simp only [unitTriangleSupport,upVertices,Finset.mem_insert,Finset.mem_singleton,
        Prod.mk.injEq] at hp ⊢
      omega
    refine ⟨(i+((N+i.natAbs+1 : ℕ) : ℤ),j), clear_east_path _ i j hclear _, ?_⟩
    apply Or.inr
    apply Or.inl
    have ha : -i ≤ (i.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -i))
    dsimp
    omega
  · have hclear : ∀ n : ℕ, (i-(n : ℤ),j) ∉ unitTriangleSupport := by
      intro n
      simp only [unitTriangleSupport,upVertices,Finset.mem_insert,Finset.mem_singleton,
        Prod.mk.injEq]
      omega
    refine ⟨(i-((N+i.natAbs+1 : ℕ) : ℤ),j), clear_west_path _ i j hclear _, ?_⟩
    apply Or.inl
    have ha : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
    dsimp
    omega

theorem unitTriangle_connected : Connected unitTriangleSupport := by
  refine ⟨⟨⟨(0,0),by decide⟩⟩,?_⟩
  intro p q
  by_cases h : p = q
  · subst q; exact Relation.ReflTransGen.refl
  · apply Relation.ReflTransGen.single
    apply (indexed_adjacency_iff _ p q).mpr
    exact up_triangle_adj 0 0 p.val q.val p.property q.property
      (fun hv => h (Subtype.ext hv))

theorem unitTriangle_unique (t : Triangles unitTriangleSupport) : t.val = (false,0,0) := by
  rcases t with ⟨⟨b,i,j⟩,ht⟩
  cases b <;>
    simp [trianglePresent,triangleVertices,upVertices,downVertices,unitTriangleSupport,
      Finset.insert_subset_iff,Finset.singleton_subset_iff,Prod.mk.injEq] at ht ⊢ <;> omega

theorem unitTriangle_triangleCount : triangleCount unitTriangleSupport = 1 := by
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨(false,0,0),by simp [trianglePresent,triangleVertices,unitTriangleSupport]⟩,?_⟩
  intro t
  exact Subtype.ext (unitTriangle_unique t)

/-- Small nontrivial end-to-end check: three cells, three contacts, one triangle. -/
theorem unitTriangle_counts :
    vertexCount unitTriangleSupport = 3 ∧ edgeCount unitTriangleSupport = 3 ∧
    triangleCount unitTriangleSupport = 1 ∧ boundaryCount unitTriangleSupport = 3 := by
  have hv : vertexCount unitTriangleSupport = 3 := by decide
  have hf := unitTriangle_triangleCount
  have hc := euler_count _ unitTriangle_connected unitTriangle_no_holes
  have hs := support_counting _ unitTriangle_connected unitTriangle_no_holes
  omega

/-- An occupied singleton has no contacts or elementary triangles. -/
theorem singleton_counts :
    edgeCount {(0,0)} = 0 ∧ triangleCount {(0,0)} = 0 ∧ boundaryCount {(0,0)} = 0 := by
  have hc : Connected {(0,0)} := by
    refine ⟨⟨⟨(0,0),by simp⟩⟩,?_⟩
    intro p q
    have hp : p.val = (0,0) := Finset.mem_singleton.mp p.property
    have hq : q.val = (0,0) := Finset.mem_singleton.mp q.property
    have h : p = q := Subtype.ext (hp.trans hq.symm)
    subst q
    exact Relation.ReflTransGen.refl
  have hs := support_counting _ hc singleton_has_no_holes
  have hv : vertexCount {(0,0)} = 1 := rfl
  omega

end Tantrix.Grid
