import Tantrix.FiniteGraph
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.FinCases

/-!
# Finite contact and triangle counts

Canonical indices enumerate each occupied contact once and each occupied
up/down triangle once. The incidence matrix is checked against the six-bit
parity definition in Grid; indexed adjacency is checked against Grid.Adj.

Rank-nullity plus the proved filling bijection gives F + n = E + 1 for
connected hole-free supports. Double counting gives 3F = P + 2I and
E = b + P + I, where b counts contacts in no occupied triangle. Thus
F + L + 2 = 2n and E + L + 3 = 3n, for L = P + 2b.
Every such zero-triangle contact is omitted by every even network; no
separate theorem identifying these contacts with bridges is required here.
-/

set_option autoImplicit false
open scoped BigOperators
open Classical
noncomputable section

namespace Tantrix.Grid

abbrev EdgeIndex := Fin 3 × Vertex
abbrev TriangleIndex := Bool × Vertex

def edgeFirst (e : EdgeIndex) : Vertex :=
  if e.1 = 2 then (e.2.1+1,e.2.2) else e.2
def edgeLast (e : EdgeIndex) : Vertex :=
  if e.1 = 0 then (e.2.1+1,e.2.2) else (e.2.1,e.2.2+1)
def edgePresent (S : Support) (e : EdgeIndex) : Prop :=
  edgeFirst e ∈ S ∧ edgeLast e ∈ S
abbrev Cells (S : Support) := {p : Vertex // p ∈ S}
abbrev Contacts (S : Support) := {e : EdgeIndex // edgePresent S e}

theorem edge_anchor_injective :
    Function.Injective (fun e : EdgeIndex => (e.1, edgeFirst e)) := by
  rintro ⟨d,i,j⟩ ⟨d',i',j'⟩ h
  have hd : d = d' := congrArg Prod.fst h
  subst d'
  have hv := congrArg Prod.snd h
  fin_cases d <;> simp_all [edgeFirst, Prod.mk.injEq]

instance contactsFintype (S : Support) : Fintype (Contacts S) :=
  Fintype.ofInjective (fun e => (e.val.1, (⟨edgeFirst e.val,e.property.1⟩ : Cells S)))
    (by
      intro e f h
      apply Subtype.ext
      apply edge_anchor_injective
      exact congrArg (fun p : Fin 3 × Cells S => (p.1,p.2.val)) h)

def firstCell (S : Support) (e : Contacts S) : Cells S := ⟨edgeFirst e.val,e.property.1⟩
def lastCell (S : Support) (e : Contacts S) : Cells S := ⟨edgeLast e.val,e.property.2⟩

def triangleVertices (t : TriangleIndex) : Finset Vertex :=
  if t.1 then downVertices t.2.1 t.2.2 else upVertices t.2.1 t.2.2
def trianglePresent (S : Support) (t : TriangleIndex) : Prop := triangleVertices t ⊆ S
abbrev Triangles (S : Support) := {t : TriangleIndex // trianglePresent S t}

def triangleAnchor (t : TriangleIndex) : Vertex :=
  if t.1 then (t.2.1+1,t.2.2) else t.2

theorem triangleAnchor_mem (t : TriangleIndex) : triangleAnchor t ∈ triangleVertices t := by
  rcases t with ⟨b,i,j⟩
  cases b <;> simp [triangleAnchor,triangleVertices,upVertices,downVertices]

theorem triangle_anchor_injective :
    Function.Injective (fun t : TriangleIndex => (t.1, triangleAnchor t)) := by
  rintro ⟨b,i,j⟩ ⟨b',i',j'⟩ h
  have hb : b = b' := congrArg Prod.fst h
  subst b'
  have hv := congrArg Prod.snd h
  cases b <;> simp_all [triangleAnchor,Prod.mk.injEq]

instance trianglesFintype (S : Support) : Fintype (Triangles S) :=
  Fintype.ofInjective
    (fun t => (t.val.1, (⟨triangleAnchor t.val,t.property (triangleAnchor_mem t.val)⟩ : Cells S)))
    (by
      intro t u h
      apply Subtype.ext
      apply triangle_anchor_injective
      exact congrArg (fun p : Bool × Cells S => (p.1,p.2.val)) h)

/-- Extend a finite indexed labelling by zero at absent indices. -/
def extend {I : Type*} {P : I → Prop} (x : {i // P i} → Bit) (i : I) : Bit :=
  if h : P i then x ⟨i,h⟩ else 0

theorem extend_at {I : Type*} {P : I → Prop} (x : {i // P i} → Bit) (i : {i // P i}) :
    extend x i.val = x i := by simp [extend,i.property]

theorem extend_sum {I : Type*} [DecidableEq I] {P : I → Prop} [Fintype {i // P i}]
    (x : {i // P i} → Bit) (i : I) :
    extend x i = ∑ j, if j.val = i then x j else 0 := by
  classical
  by_cases hi : P i
  · rw [Finset.sum_eq_single (⟨i,hi⟩ : {i // P i})]
    · simp [extend,hi]
    · intro j _ hj
      have hji : j.val ≠ i := fun h => hj (Subtype.ext h)
      simp [hji]
    · simp
  · have hn : ∀ j : {i // P i}, j.val ≠ i := by
      intro j h
      exact hi (h ▸ j.property)
    simp [extend,hi,hn]

def decodeEdges (S : Support) (x : Contacts S → Bit) : Edges where
  horizontal i j := extend x (0,i,j)
  vertical i j := extend x (1,i,j)
  diagonal i j := extend x (2,i,j)

def edgeValue (E : Edges) (e : EdgeIndex) : Bit :=
  if e.1 = 0 then E.horizontal e.2.1 e.2.2
  else if e.1 = 1 then E.vertical e.2.1 e.2.2 else E.diagonal e.2.1 e.2.2

theorem edgeValue_decode (S : Support) (x : Contacts S → Bit) (e : EdgeIndex) :
    edgeValue (decodeEdges S x) e = extend x e := by
  rcases e with ⟨d,i,j⟩
  fin_cases d <;> simp [edgeValue,decodeEdges]

theorem decode_supported (S : Support) (x : Contacts S → Bit) :
    (decodeEdges S x).Supported S := by
  refine ⟨?_,?_,?_⟩ <;> intro i j h <;>
    rcases h with h | h <;>
    simp only [decodeEdges,extend,edgePresent,edgeFirst,edgeLast] <;>
    simp_all

def decodeFilling (S : Support) (x : Triangles S → Bit) : Filling where
  up i j := extend x (false,i,j)
  down i j := extend x (true,i,j)

def triangleValue (R : Filling) (t : TriangleIndex) : Bit :=
  if t.1 then R.down t.2.1 t.2.2 else R.up t.2.1 t.2.2

theorem triangleValue_decode (S : Support) (x : Triangles S → Bit) (t : TriangleIndex) :
    triangleValue (decodeFilling S x) t = extend x t := by
  cases t with | mk b p => cases b <;> rfl

theorem decode_contained (S : Support) (x : Triangles S → Bit) :
    (decodeFilling S x).Contained S := by
  intro i j
  constructor
  · intro h
    have hp : trianglePresent S (false,i,j) := by
      by_contra hn
      exact h (by simp [decodeFilling,extend,hn])
    exact hp
  · intro h
    have hp : trianglePresent S (true,i,j) := by
      by_contra hn
      exact h (by simp [decodeFilling,extend,hn])
    exact hp

def star (p : Vertex) : Fin 6 → EdgeIndex :=
  ![(0,p.1-1,p.2), (0,p.1,p.2), (1,p.1,p.2-1),
    (1,p.1,p.2), (2,p.1-1,p.2), (2,p.1,p.2-1)]

theorem star_incidence (p : Vertex) (e : EdgeIndex) :
    (∑ k : Fin 6, if star p k = e then (1 : Bit) else 0) =
      (if edgeFirst e = p then 1 else 0) + (if edgeLast e = p then 1 else 0) := by
  rcases p with ⟨i,j⟩
  rcases e with ⟨d,k,l⟩
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases d <;> simp only [star,Matrix.cons_val_zero,Matrix.cons_val_succ,
    edgeFirst,edgeLast,Prod.mk.injEq] <;> norm_num
  all_goals
    have h1 : (i-1 = k ∧ j = l) ↔ (k+1 = i ∧ l = j) := by omega
    have h2 : (i = k ∧ j-1 = l) ↔ (k = i ∧ l+1 = j) := by omega
    have h3 : (i = k ∧ j = l) ↔ (k = i ∧ l = j) := by omega
    simp only [h1,h2,h3] <;> ac_rfl

def incidence (S : Support) : Matrix (Contacts S) (Cells S) Bit :=
  FiniteGraph.incidence (firstCell S) (lastCell S)

theorem incidence_parity (S : Support) (x : Contacts S → Bit) (p : Cells S) :
    (incidence S).transpose.mulVec x p = ∑ k : Fin 6, extend x (star p.val k) := by
  change (∑ e : Contacts S, (incidence S) e p * x e) = _
  simp_rw [extend_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have hs := star_incidence p.val e.val
  have hc : (∑ k : Fin 6, if e.val = star p.val k then x e else 0) =
      ((if edgeFirst e.val = p.val then 1 else 0) +
       (if edgeLast e.val = p.val then 1 else 0)) * x e := by
    rw [← hs,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    simp [eq_comm,ite_mul]
  simpa only [incidence,FiniteGraph.incidence,firstCell,lastCell,
    Subtype.ext_iff] using! hc.symm

theorem decode_even_iff (S : Support) (x : Contacts S → Bit) :
    (decodeEdges S x).Even ↔ (incidence S).transpose.mulVec x = 0 := by
  have heq : ∀ p : Cells S, (incidence S).transpose.mulVec x p =
      (decodeEdges S x).horizontal (p.val.1-1) p.val.2 +
      (decodeEdges S x).horizontal p.val.1 p.val.2 +
      (decodeEdges S x).vertical p.val.1 (p.val.2-1) +
      (decodeEdges S x).vertical p.val.1 p.val.2 +
      (decodeEdges S x).diagonal (p.val.1-1) p.val.2 +
      (decodeEdges S x).diagonal p.val.1 (p.val.2-1) := by
    intro p
    rw [incidence_parity]
    simp [star,Fin.sum_univ_succ,decodeEdges,add_assoc]
  constructor
  · intro h
    funext p
    rw [heq]
    exact h p.val.1 p.val.2
  · intro h i j
    by_cases hp : (i,j) ∈ S
    · simpa only [heq,Pi.zero_apply] using congrFun h (⟨(i,j),hp⟩ : Cells S)
    · have hs := decode_supported S x
      have h0 := hs.1 (i-1) j (Or.inr (by simpa using hp))
      have h1 := hs.1 i j (Or.inl hp)
      have h2 := hs.2.1 i (j-1) (Or.inr (by simpa using hp))
      have h3 := hs.2.1 i j (Or.inl hp)
      have h4 := hs.2.2 (i-1) j (Or.inl (by simpa using hp))
      have h5 := hs.2.2 i (j-1) (Or.inr (by simpa using hp))
      rw [h0,h1,h2,h3,h4,h5]
      simp

theorem decode_edges_inverse (S : Support) (E : Edges) (hs : E.Supported S) :
    decodeEdges S (fun e => edgeValue E e.val) = E := by
  apply Edges.ext <;> funext i j
  all_goals simp only [decodeEdges,extend]
  all_goals split_ifs with h
  all_goals try { simp [edgeValue] }
  · have hn : (i,j) ∉ S ∨ (i+1,j) ∉ S := by
      apply not_and_or.mp
      simpa [edgePresent,edgeFirst,edgeLast] using h
    exact (hs.1 i j hn).symm
  · have hn : (i,j) ∉ S ∨ (i,j+1) ∉ S := by
      apply not_and_or.mp
      simpa [edgePresent,edgeFirst,edgeLast] using h
    exact (hs.2.1 i j hn).symm
  · have hn : (i+1,j) ∉ S ∨ (i,j+1) ∉ S := by
      apply not_and_or.mp
      simpa [edgePresent,edgeFirst,edgeLast] using h
    exact (hs.2.2 i j hn).symm

theorem decode_filling_inverse (S : Support) (R : Filling) (hc : R.Contained S) :
    decodeFilling S (fun t => triangleValue R t.val) = R := by
  apply Filling.ext <;> funext i j
  all_goals simp only [decodeFilling,extend]
  all_goals split_ifs with h
  all_goals try { simp [triangleValue] }
  · by_contra hz
    apply h
    exact (hc i j).1 (Ne.symm hz)
  · by_contra hz
    apply h
    exact (hc i j).2 (Ne.symm hz)

def fillingEquiv (S : Support) : (Triangles S → Bit) ≃ InsideFillings S where
  toFun x := ⟨decodeFilling S x, decode_contained S x⟩
  invFun R t := triangleValue R.val t.val
  left_inv x := by
    funext t
    exact (triangleValue_decode S x t.val).trans (extend_at x t)
  right_inv R := Subtype.ext (decode_filling_inverse S R.val R.property)

def networkEquiv (S : Support) :
    LinearMap.ker (incidence S).transpose.mulVecLin ≃ EvenNetworks S where
  toFun x := ⟨decodeEdges S x.val, (decode_even_iff S x.val).mpr x.property,
    decode_supported S x.val⟩
  invFun E := ⟨fun e => edgeValue E.val e.val, (decode_even_iff S _).mp (by
    rw [decode_edges_inverse S E.val E.property.2]
    exact E.property.1)⟩
  left_inv x := by
    apply Subtype.ext
    funext e
    exact (edgeValue_decode S x.val e.val).trans (extend_at x.val e)
  right_inv E := Subtype.ext (decode_edges_inverse S E.val E.property.2)

/-- All quantities are cardinalities of explicit occupied lattice objects. -/
def vertexCount (S : Support) : ℕ := S.card
def edgeCount (S : Support) : ℕ := Fintype.card (Contacts S)
def triangleCount (S : Support) : ℕ := Fintype.card (Triangles S)

theorem filling_dimension (S : Support) (hn : NoHoles S) :
    Module.finrank Bit (LinearMap.ker (incidence S).transpose.mulVecLin) =
      triangleCount S := by
  have he : Nonempty ((Triangles S → Bit) ≃
      LinearMap.ker (incidence S).transpose.mulVecLin) :=
    ⟨(fillingEquiv S).trans ((Equiv.ofBijective (boundaryMap S)
      (boundary_bijective S hn)).trans (networkEquiv S).symm)⟩
  obtain ⟨e⟩ := he
  have hcard := Nat.card_congr e
  rw [Nat.card_fun, Module.natCard_eq_pow_finrank (K := Bit)
    (V := LinearMap.ker (incidence S).transpose.mulVecLin)] at hcard
  simp only [Nat.card_eq_fintype_card, ZMod.card] at hcard
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2) hcard).symm

/-- Connectedness is a finite-walk condition, not a counting hypothesis. -/
def Connected (S : Support) : Prop := FiniteGraph.Connected (firstCell S) (lastCell S)

theorem euler_count (S : Support) (hc : Connected S) (hn : NoHoles S) :
    triangleCount S + vertexCount S = edgeCount S + 1 := by
  have h := FiniteGraph.cycle_dimension (firstCell S) (lastCell S) hc
  rw [← incidence, filling_dimension S hn] at h
  simpa only [Fintype.card_coe,vertexCount,edgeCount] using h

def upAt (e : EdgeIndex) : TriangleIndex := (false,e.2)
def downAt (e : EdgeIndex) : TriangleIndex :=
  if e.1 = 0 then (true,e.2.1,e.2.2-1)
  else if e.1 = 1 then (true,e.2.1-1,e.2.2) else (true,e.2)

def triangleSide (t : TriangleIndex) (k : Fin 3) : EdgeIndex :=
  if t.1 then
    if k = 0 then (k,t.2.1,t.2.2+1)
    else if k = 1 then (k,t.2.1+1,t.2.2) else (k,t.2)
  else (k,t.2)

theorem triangleSide_present (S : Support) (t : Triangles S) (k : Fin 3) :
    edgePresent S (triangleSide t.val k) := by
  rcases t with ⟨⟨b,i,j⟩,ht⟩
  cases b <;>
    simp only [trianglePresent,triangleVertices,Bool.false_eq_true,ite_false,ite_true,
      upVertices,downVertices,Finset.insert_subset_iff,Finset.singleton_subset_iff] at ht <;>
    fin_cases k <;> simp_all [edgePresent,edgeFirst,edgeLast,triangleSide]

theorem triangleSide_incidence (t : TriangleIndex) (e : EdgeIndex) :
    (∑ k : Fin 3, if triangleSide t k = e then (1 : ℕ) else 0) =
      (if t = upAt e then 1 else 0) + (if t = downAt e then 1 else 0) := by
  rcases t with ⟨b,i,j⟩
  rcases e with ⟨d,k,l⟩
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  cases b <;> fin_cases d <;>
    simp [triangleSide,upAt,downAt,Prod.mk.injEq] <;>
    split_ifs <;> omega

theorem present_sum {I : Type*} [DecidableEq I] {P : I → Prop}
    [Fintype {i // P i}] (i : I) :
    (if P i then (1 : ℕ) else 0) = ∑ j : {i // P i}, if j.val = i then 1 else 0 := by
  by_cases hi : P i
  · rw [Finset.sum_eq_single (⟨i,hi⟩ : {i // P i})]
    · simp [hi]
    · intro j _ hj
      have hji : j.val ≠ i := fun h => hj (Subtype.ext h)
      simp [hji]
    · simp
  · have hn : ∀ j : {i // P i}, j.val ≠ i := by
      intro j h
      exact hi (h ▸ j.property)
    simp [hi,hn]

/-- Number (zero, one or two) of occupied elementary triangles at a contact. -/
def triangleDegree (S : Support) (e : EdgeIndex) : ℕ :=
  (if trianglePresent S (upAt e) then 1 else 0) +
  (if trianglePresent S (downAt e) then 1 else 0)

theorem triangleDegree_le_two (S : Support) (e : EdgeIndex) : triangleDegree S e ≤ 2 := by
  unfold triangleDegree
  split_ifs <;> omega

theorem triangle_incidence_count (S : Support) :
    (∑ e : Contacts S, triangleDegree S e.val) = 3 * triangleCount S := by
  unfold triangleDegree
  simp_rw [present_sum]
  simp_rw [← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  have htri : ∀ t : Triangles S,
      (∑ e : Contacts S, ((if t.val = upAt e.val then 1 else 0) +
        (if t.val = downAt e.val then 1 else 0))) = 3 := by
    intro t
    simp_rw [← triangleSide_incidence]
    rw [Finset.sum_comm]
    have hside : ∀ k : Fin 3,
        (∑ e : Contacts S, if triangleSide t.val k = e.val then (1 : ℕ) else 0) = 1 := by
      intro k
      have h := present_sum (P := edgePresent S) (triangleSide t.val k)
      simpa only [triangleSide_present S t k,ite_true,eq_comm] using h.symm
    simp_rw [hside]
    simp
  simp_rw [htri]
  simp [triangleCount,Nat.mul_comm]

/-- Counts of contacts meeting zero, one and two occupied triangles. -/
def bareCount (S : Support) : ℕ := ∑ e : Contacts S, if triangleDegree S e.val = 0 then 1 else 0
def perimeterCount (S : Support) : ℕ := ∑ e : Contacts S, if triangleDegree S e.val = 1 then 1 else 0
def internalCount (S : Support) : ℕ := ∑ e : Contacts S, if triangleDegree S e.val = 2 then 1 else 0
def boundaryCount (S : Support) : ℕ := perimeterCount S + 2 * bareCount S

theorem contact_partition (S : Support) :
    edgeCount S = bareCount S + perimeterCount S + internalCount S := by
  unfold edgeCount bareCount perimeterCount internalCount
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  have h : ∀ e : Contacts S,
      (if triangleDegree S e.val = 0 then 1 else 0) +
      (if triangleDegree S e.val = 1 then 1 else 0) +
      (if triangleDegree S e.val = 2 then 1 else 0) = (1 : ℕ) := by
    intro e
    have hb := triangleDegree_le_two S e.val
    interval_cases triangleDegree S e.val <;> simp
  simp_rw [h]
  simp

theorem triangle_partition (S : Support) :
    3 * triangleCount S = perimeterCount S + 2 * internalCount S := by
  rw [← triangle_incidence_count]
  unfold perimeterCount internalCount
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hb := triangleDegree_le_two S e.val
  interval_cases triangleDegree S e.val <;> simp

theorem support_counting (S : Support) (hc : Connected S) (hn : NoHoles S) :
    triangleCount S + boundaryCount S + 2 = 2 * vertexCount S ∧
    edgeCount S + boundaryCount S + 3 = 3 * vertexCount S := by
  have h1 := euler_count S hc hn
  have h2 := contact_partition S
  have h3 := triangle_partition S
  unfold boundaryCount
  omega

def selectedCount (S : Support) (x : Contacts S → Bit) : ℕ :=
  ∑ e, if x e = 0 then 0 else 1
def omittedCount (S : Support) (x : Contacts S → Bit) : ℕ :=
  ∑ e, if x e = 0 then 1 else 0

theorem selection_partition (S : Support) (x : Contacts S → Bit) :
    selectedCount S x + omittedCount S x = edgeCount S := by
  unfold selectedCount omittedCount edgeCount
  rw [← Finset.sum_add_distrib]
  have h : ∀ e, (if x e = 0 then 0 else 1) + (if x e = 0 then 1 else 0) = (1 : ℕ) := by
    intro e
    split_ifs <;> rfl
  simp_rw [h]
  simp

theorem boundary_edgeValue (R : Filling) (e : EdgeIndex) :
    edgeValue R.boundary e = triangleValue R (upAt e) + triangleValue R (downAt e) := by
  rcases e with ⟨d,i,j⟩
  fin_cases d <;> simp [edgeValue,Filling.boundary,triangleValue,upAt,downAt]

theorem triangleValue_zero_of_absent (S : Support) (R : Filling) (hc : R.Contained S)
    (t : TriangleIndex) (ht : ¬ trianglePresent S t) : triangleValue R t = 0 := by
  rcases t with ⟨b,i,j⟩
  cases b
  · by_contra h
    exact ht ((hc i j).1 h)
  · by_contra h
    exact ht ((hc i j).2 h)

/-- Zero-triangle contacts cannot be selected by any even supported network.
This is the bridge-omission fact needed for counting, without a bridge API. -/
theorem bare_contact_omitted (S : Support) (hn : NoHoles S) (x : Contacts S → Bit)
    (he : (decodeEdges S x).Even) (e : Contacts S) (hb : triangleDegree S e.val = 0) :
    x e = 0 := by
  obtain ⟨R,⟨_,hr,hc⟩,_⟩ := support_filling (decodeEdges S x) S he (decode_supported S x) hn
  have hu : ¬ trianglePresent S (upAt e.val) := by
    unfold triangleDegree at hb
    split_ifs at hb <;> omega
  have hd : ¬ trianglePresent S (downAt e.val) := by
    by_contra hd
    simp [triangleDegree,hu,hd] at hb
  have h := boundary_edgeValue R e.val
  rw [hr,edgeValue_decode,extend_at,triangleValue_zero_of_absent S R hc _ hu,
    triangleValue_zero_of_absent S R hc _ hd,add_zero] at h
  exact h

theorem bare_le_omitted (S : Support) (hn : NoHoles S) (x : Contacts S → Bit)
    (he : (decodeEdges S x).Even) : bareCount S ≤ omittedCount S x := by
  apply Finset.sum_le_sum
  intro e _
  by_cases hb : triangleDegree S e.val = 0
  · simp [hb,bare_contact_omitted S hn x he e hb]
  · simp [hb]

/-- The two exact counting premises used by the conditional 136 theorem. -/
theorem counting_56 (S : Support) (hc : Connected S) (hn : NoHoles S)
    (h56 : S.card = 56) (x : Contacts S → Bit) :
    triangleCount S + boundaryCount S = 110 ∧
    selectedCount S x + boundaryCount S + omittedCount S x = 165 := by
  have h := support_counting S hc hn
  have hp := selection_partition S x
  unfold vertexCount at h
  omega

theorem edge_endpoints_adjacent (e : EdgeIndex) : Adj (edgeFirst e) (edgeLast e) := by
  rcases e with ⟨d,i,j⟩
  fin_cases d <;> simp [Adj,edgeFirst,edgeLast]

theorem edge_endpoints_distinct (e : EdgeIndex) : edgeFirst e ≠ edgeLast e := by
  intro h
  have ha := edge_endpoints_adjacent e
  rw [h] at ha
  exact adj_irrefl _ ha

theorem adjacent_iff_edge (p q : Vertex) : Adj p q ↔
    ∃ e : EdgeIndex, (edgeFirst e = p ∧ edgeLast e = q) ∨
      (edgeFirst e = q ∧ edgeLast e = p) := by
  constructor
  · rcases p with ⟨i,j⟩
    intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(0,i,j),Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨(1,i,j),Or.inl ⟨rfl,rfl⟩⟩
    · refine ⟨(2,i-1,j),Or.inl ?_⟩; simp [edgeFirst,edgeLast]
    · refine ⟨(0,i-1,j),Or.inr ?_⟩; simp [edgeFirst,edgeLast]
    · refine ⟨(1,i,j-1),Or.inr ?_⟩; simp [edgeFirst,edgeLast]
    · refine ⟨(2,i,j-1),Or.inr ?_⟩; simp [edgeFirst,edgeLast]
  · rintro ⟨e,h | h⟩
    · rw [← h.1,← h.2]; exact edge_endpoints_adjacent e
    · rw [← h.1,← h.2]; exact adj_symmetric _ _ (edge_endpoints_adjacent e)

theorem indexed_adjacency_iff (S : Support) (p q : Cells S) :
    FiniteGraph.Adj (firstCell S) (lastCell S) p q ↔ Adj p.val q.val := by
  constructor
  · rintro ⟨e,h | h⟩
    · apply (adjacent_iff_edge _ _).mpr
      exact ⟨e.val,Or.inl ⟨congrArg Subtype.val h.1,congrArg Subtype.val h.2⟩⟩
    · apply (adjacent_iff_edge _ _).mpr
      exact ⟨e.val,Or.inr ⟨congrArg Subtype.val h.1,congrArg Subtype.val h.2⟩⟩
  · intro h
    obtain ⟨e,h | h⟩ := (adjacent_iff_edge _ _).mp h
    · have he : edgePresent S e := by
        exact ⟨h.1 ▸ p.property,h.2 ▸ q.property⟩
      exact ⟨⟨e,he⟩,Or.inl ⟨Subtype.ext h.1,Subtype.ext h.2⟩⟩
    · have he : edgePresent S e := by
        exact ⟨h.1 ▸ q.property,h.2 ▸ p.property⟩
      exact ⟨⟨e,he⟩,Or.inr ⟨Subtype.ext h.1,Subtype.ext h.2⟩⟩

theorem edge_same_contact_iff (e f : EdgeIndex) :
    ((edgeFirst e = edgeFirst f ∧ edgeLast e = edgeLast f) ∨
      (edgeFirst e = edgeLast f ∧ edgeLast e = edgeFirst f)) ↔ e = f := by
  rcases e with ⟨d,i,j⟩
  rcases f with ⟨d',k,l⟩
  fin_cases d <;> fin_cases d' <;> simp [edgeFirst,edgeLast,Prod.mk.injEq] <;> omega

end Tantrix.Grid
