import Tantrix.TileInventory
import Tantrix.Disconnected
import Tantrix.GridExamples

/-!
# A coloured 136-point Tantrix construction

Milan Kuchtiak's published arrangement, transcribed from
https://www.jaapsch.net/puzzles/images/tantrix/unslvloop.gif
(source page: https://www.jaapsch.net/puzzles/tantrix.htm).

The diagram's centre for lattice (i,j) is pixel (30+47(i+j),269+27(j-i)).
The support is the size-10 triangle plus (-1,1).
Source GIF SHA-256: 3b92f686887acf3ec4e5181c56cbbac942c545bdbb99f3a9b9b91ea132527ea9.
Every certificate below is checked by Lean's kernel, not by the image reader.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
open scoped BigOperators

namespace Tantrix.Loops.Coloured136
open Grid

def support : Support :=
  insert (-1,1)
    (((Finset.Icc (0 : ℤ) 9).product (Finset.Icc (0 : ℤ) 9)).filter
      (fun p => p.1+p.2 ≤ 9))

@[simp] theorem mem_support (i j : ℤ) :
    (i,j) ∈ support ↔ (i = -1 ∧ j = 1) ∨ (0 ≤ i ∧ 0 ≤ j ∧ i+j ≤ 9) := by
  simp only [support,Finset.mem_insert,Finset.mem_filter,Prod.mk.injEq]
  simp only [Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]
  omega

theorem card_support : support.card = 56 := by decide

/-- Every empty cell has a clear horizontal ray; no holes are assumed. -/
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
      simp only [mem_support] at hp ⊢
      omega
    refine ⟨(i-((N+i.natAbs+1 : ℕ) : ℤ),j), clear_west_path _ i j hclear _, ?_⟩
    apply Or.inl
    have ha : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
    dsimp
    omega

def centres : Fin 56 → Vertex :=
  ![(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),
    (0,8),(0,9),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),
    (1,6),(1,7),(1,8),(2,0),(2,1),(2,2),(2,3),(2,4),
    (2,5),(2,6),(2,7),(3,0),(3,1),(3,2),(3,3),(3,4),
    (3,5),(3,6),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),
    (5,0),(5,1),(5,2),(5,3),(5,4),(6,0),(6,1),(6,2),
    (6,3),(7,0),(7,1),(7,2),(8,0),(8,1),(9,0),(-1,1)]

def lookup (p : Vertex) : Fin 56 :=
  if p.1 < 0 then 55 else
    ⟨(p.1.toNat*(21-p.1.toNat)/2+p.2.toNat)%56,Nat.mod_lt _ (by decide)⟩

def cell (k : Fin 56) : Cells support :=
  ⟨centres k,by decide +revert⟩

@[simp] theorem lookup_centres (k : Fin 56) : lookup (centres k) = k := by decide +revert

theorem centres_lookup (p : Cells support) : centres (lookup p.val) = p.val := by
  rcases p with ⟨⟨i,j⟩,hp⟩
  rcases (mem_support i j).mp hp with ⟨rfl,rfl⟩ | ⟨hi,hj,hs⟩
  · rfl
  · have hi9 : i ≤ 9 := by omega
    have hj9 : j ≤ 9 := by omega
    interval_cases i <;> interval_cases j <;> norm_num [lookup,centres] at *

def cellEquiv : Fin 56 ≃ Cells support where
  toFun := cell
  invFun p := lookup p.val
  left_inv := lookup_centres
  right_inv p := Subtype.ext (centres_lookup p)

/-- For each grid cell, its zero-based numbered tile and rotation. -/
def tileIds : Fin 56 → Fin 56 :=
  ![19,54,28,42,6,17,48,36,37,51,53,44,49,31,
    55,3,40,27,21,23,50,52,41,24,33,39,16,1,
    2,30,34,7,26,22,11,9,20,47,8,25,15,0,
    43,14,18,12,29,38,46,10,5,32,35,4,13,45]

def tileIdsInverse : Fin 56 → Fin 56 :=
  ![41,27,28,15,53,50,4,31,38,35,49,34,45,54,
    43,40,26,5,44,0,36,18,33,19,23,39,32,17,
    2,46,29,13,51,24,30,52,7,8,47,25,16,22,
    3,42,11,55,48,37,6,12,20,9,21,10,1,14]

def tileIdEquiv : Fin 56 ≃ Fin 56 where
  toFun := tileIds
  invFun := tileIdsInverse
  left_inv := by decide
  right_inv := by decide

def rotations : Fin 56 → Fin 6 :=
  ![3,1,4,2,4,4,1,4,4,2,2,4,4,5,
    1,4,1,2,3,5,5,4,3,4,5,4,0,2,
    4,4,5,1,2,2,2,5,0,3,4,3,2,5,
    5,0,0,5,2,2,0,2,5,0,2,3,0,1]

/-- Three strands per tile: colour, entry-side candidate, exit-side candidate.
Endpoint choices just orient each strand; both traversal directions are allowed. -/
def tileData : Fin 56 → Fin 3 → Colour × Side × Side := ![
  ![(0,0,2),(2,1,4),(3,3,5)], -- (0,0), tile 20
  ![(1,1,5),(2,0,3),(3,2,4)], -- (0,1), tile 55
  ![(0,0,4),(1,3,5),(2,1,2)], -- (0,2), tile 29
  ![(1,2,5),(2,0,4),(3,1,3)], -- (0,3), tile 43
  ![(0,3,5),(1,0,4),(3,1,2)], -- (0,4), tile 7
  ![(0,1,2),(2,3,5),(3,0,4)], -- (0,5), tile 18
  ![(1,1,5),(2,2,3),(3,0,4)], -- (0,6), tile 49
  ![(0,3,5),(1,0,4),(2,1,2)], -- (0,7), tile 37
  ![(0,1,2),(1,0,4),(2,3,5)], -- (0,8), tile 38
  ![(1,0,3),(2,2,5),(3,1,4)], -- (0,9), tile 52
  ![(1,1,4),(2,0,3),(3,2,5)], -- (1,0), tile 54
  ![(1,0,4),(2,2,5),(3,1,3)], -- (1,1), tile 45
  ![(1,4,5),(2,0,3),(3,1,2)], -- (1,2), tile 50
  ![(0,1,4),(2,2,3),(3,0,5)], -- (1,3), tile 32
  ![(1,1,5),(2,2,4),(3,0,3)], -- (1,4), tile 56
  ![(0,0,3),(1,4,5),(3,1,2)], -- (1,5), tile 4
  ![(0,2,4),(1,0,3),(2,1,5)], -- (1,6), tile 41
  ![(0,1,3),(1,2,5),(2,0,4)], -- (1,7), tile 28
  ![(0,0,2),(2,4,5),(3,1,3)], -- (1,8), tile 22
  ![(0,2,5),(1,0,1),(2,3,4)], -- (2,0), tile 24
  ![(1,1,4),(2,2,3),(3,0,5)], -- (2,1), tile 51
  ![(1,3,5),(2,1,2),(3,0,4)], -- (2,2), tile 53
  ![(0,0,1),(1,2,4),(2,3,5)], -- (2,3), tile 42
  ![(0,1,3),(1,0,4),(2,2,5)], -- (2,4), tile 25
  ![(0,2,3),(2,1,4),(3,0,5)], -- (2,5), tile 34
  ![(0,1,2),(1,4,5),(2,0,3)], -- (2,6), tile 40
  ![(0,0,5),(2,2,4),(3,1,3)], -- (2,7), tile 17
  ![(0,2,5),(1,0,1),(3,3,4)], -- (3,0), tile 2
  ![(0,1,3),(1,0,4),(3,2,5)], -- (3,1), tile 3
  ![(0,1,2),(2,0,4),(3,3,5)], -- (3,2), tile 31
  ![(0,0,5),(2,1,4),(3,2,3)], -- (3,3), tile 35
  ![(0,0,3),(1,1,5),(3,2,4)], -- (3,4), tile 8
  ![(0,2,5),(1,1,4),(2,0,3)], -- (3,5), tile 27
  ![(0,0,4),(2,2,5),(3,1,3)], -- (3,6), tile 23
  ![(0,2,5),(1,0,3),(3,1,4)], -- (4,0), tile 12
  ![(0,0,5),(1,1,2),(3,3,4)], -- (4,1), tile 10
  ![(0,0,4),(2,1,3),(3,2,5)], -- (4,2), tile 21
  ![(1,4,5),(2,0,2),(3,1,3)], -- (4,3), tile 48
  ![(0,4,5),(1,0,3),(3,1,2)], -- (4,4), tile 9
  ![(0,1,3),(1,0,2),(2,4,5)], -- (4,5), tile 26
  ![(0,3,4),(2,2,5),(3,0,1)], -- (5,0), tile 16
  ![(0,1,2),(1,0,5),(3,3,4)], -- (5,1), tile 1
  ![(1,1,4),(2,0,5),(3,2,3)], -- (5,2), tile 44
  ![(0,4,5),(2,1,3),(3,0,2)], -- (5,3), tile 15
  ![(0,1,3),(2,2,4),(3,0,5)], -- (5,4), tile 19
  ![(0,2,5),(1,3,4),(3,0,1)], -- (6,0), tile 13
  ![(0,0,1),(1,2,5),(2,3,4)], -- (6,1), tile 30
  ![(0,1,4),(1,0,5),(2,2,3)], -- (6,2), tile 39
  ![(1,1,3),(2,0,2),(3,4,5)], -- (6,3), tile 47
  ![(0,2,5),(1,1,4),(3,0,3)], -- (7,0), tile 11
  ![(0,0,5),(1,1,4),(3,2,3)], -- (7,1), tile 6
  ![(0,0,5),(2,1,3),(3,2,4)], -- (7,2), tile 33
  ![(0,1,4),(1,0,3),(2,2,5)], -- (8,0), tile 36
  ![(0,4,5),(1,0,2),(3,1,3)], -- (8,1), tile 5
  ![(0,0,4),(1,1,3),(3,2,5)], -- (9,0), tile 14
  ![(1,0,3),(2,1,5),(3,2,4)] -- (-1,1), tile 46
]

def endsTable (k : Fin 56) (a : Fin 3 × Bool) : Side :=
  if a.2 then (tileData k a.1).2.2 else (tileData k a.1).2.1

def inverseSide (k : Fin 56) (s : Side) : Fin 3 × Bool :=
  if s = endsTable k (0,false) then (0,false)
  else if s = endsTable k (0,true) then (0,true)
  else if s = endsTable k (1,false) then (1,false)
  else if s = endsTable k (1,true) then (1,true)
  else if s = endsTable k (2,false) then (2,false)
  else (2,true)

def tile (k : Fin 56) : Tile where
  ends := {
    toFun := endsTable k
    invFun := inverseSide k
    left_inv := by decide +revert
    right_inv := by decide +revert }
  colour := ⟨fun a => (tileData k a).1,by decide +revert⟩

def sideColour (k : Fin 56) (s : Side) : Colour :=
  (tile k).colour ((tile k).ends.symm s).1

theorem tile_pattern (k : Fin 56) (d : Fin 6) :
    sideColour k (Inventory.clockwiseSide d) =
      Inventory.pattern (tileIds k) (d+rotations k) := by decide +revert

def tileAt (p : Cells support) : Tile := tile (lookup p.val)

/-- Exactly the 135 triangle contacts and the extra tile's two contacts. -/
def contactIndices : Finset EdgeIndex :=
  {(0,-1,1),(2,-1,0)} ∪
    (Finset.univ ×ˢ (((Finset.Icc (0 : ℤ) 8) ×ˢ (Finset.Icc (0 : ℤ) 8)).filter
      (fun p => p.1+p.2 ≤ 8)))

theorem mem_contactIndices (e : EdgeIndex) :
    e ∈ contactIndices ↔ edgePresent support e := by
  rcases e with ⟨d,i,j⟩
  fin_cases d <;>
    simp [contactIndices,edgePresent,edgeFirst,edgeLast,mem_support,Prod.mk.injEq] <;> omega

set_option maxHeartbeats 2000000 in
theorem triangle_contacts_match (d : Fin 3) (i j : Fin 9) (h : i.val+j.val ≤ 8) :
    sideColour (lookup (edgeFirst (d,(i.val : ℤ),(j.val : ℤ)))) (![1,3,4] d) =
      sideColour (lookup (edgeLast (d,(i.val : ℤ),(j.val : ℤ)))) (![0,2,5] d) := by
  decide +revert

theorem contacts_match : ∀ e ∈ contactIndices,
    sideColour (lookup (edgeFirst e)) (![1,3,4] e.1) =
      sideColour (lookup (edgeLast e)) (![0,2,5] e.1) := by
  rintro ⟨d,i,j⟩ he
  simp only [contactIndices,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    Finset.mem_product,Finset.mem_univ,true_and,Finset.mem_filter,Finset.mem_Icc] at he
  rcases he with he | ⟨⟨⟨hi,hi8⟩,⟨hj,hj8⟩⟩,hs⟩
  · rcases he with he | he <;> cases he <;> decide
  · have hi' : i.toNat < 9 := by omega
    have hj' : j.toNat < 9 := by omega
    have hsum : i.toNat+j.toNat ≤ 8 := by
      change i+j ≤ 8 at hs
      omega
    simpa only [Int.toNat_of_nonneg hi,Int.toNat_of_nonneg hj] using
      triangle_contacts_match d ⟨i.toNat,hi'⟩ ⟨j.toNat,hj'⟩ hsum

def placement : Placement support where
  tile := tileAt
  matching e := by
    change sideColour (lookup (edgeFirst e.val)) (![1,3,4] e.val.1) =
      sideColour (lookup (edgeLast e.val)) (![0,2,5] e.val.1)
    exact contacts_match e.val ((mem_contactIndices e.val).mpr e.property)

theorem uses_full_set : Inventory.UsesFullSet placement := by
  refine ⟨cellEquiv.symm.trans tileIdEquiv,fun p => rotations (lookup p.val),?_⟩
  intro p d
  change sideColour (lookup p.val) (Inventory.clockwiseSide d) =
    Inventory.pattern (tileIds (lookup p.val)) (d+rotations (lookup p.val))
  exact tile_pattern _ _
/-- Red, blue, green and yellow lengths, respectively. -/
def loopLength : Colour → ℕ := ![33,35,38,30]

/-- Each occurrence gives cell index, strand index and its entering endpoint.
The four cyclic lists are the concrete lower-bound certificate. -/
def loopData (c : Colour) : Fin (loopLength c) → Fin 56 × Fin 3 × Bool :=
  match c with
  | ⟨0,_⟩ => ![(4,0,true),(5,0,true),(15,0,false),(16,0,false),(7,0,true),
      (8,0,true),(18,0,false),(17,0,true),(26,0,false),(33,0,true),
      (25,0,false),(24,0,true),(23,0,true),(31,0,false),(32,0,false),
      (38,0,false),(43,0,false),(47,0,true),(51,0,false),(53,0,false),
      (54,0,true),(52,0,false),(50,0,true),(46,0,true),(41,0,false),
      (40,0,false),(35,0,true),(28,0,false),(29,0,true),(36,0,false),
      (30,0,true),(22,0,true),(13,0,false)]
  | ⟨1,_⟩ => ![(1,0,true),(11,0,false),(2,1,true),(3,0,false),(12,0,false),
      (20,0,true),(28,1,false),(21,0,true),(22,1,false),(14,0,true),
      (23,1,false),(15,1,true),(6,0,true),(16,1,false),(17,1,false),
      (25,1,false),(32,1,true),(39,1,false),(38,1,true),(31,1,false),
      (37,0,false),(42,0,true),(47,1,false),(50,1,true),(53,1,false),
      (52,1,true),(49,1,false),(46,1,true),(45,1,false),(41,1,true),
      (35,1,false),(34,1,true),(27,1,true),(19,1,true),(10,0,false)]
  | ⟨2,_⟩ => ![(0,1,true),(10,1,false),(11,1,false),(19,2,true),(20,1,false),
      (21,1,true),(29,1,false),(22,2,true),(23,2,false),(30,1,true),
      (37,1,false),(36,1,true),(42,1,false),(46,2,true),(47,2,false),
      (48,1,true),(43,1,false),(44,1,false),(39,2,true),(33,1,true),
      (32,2,true),(24,1,false),(16,2,true),(25,2,false),(26,1,false),
      (18,1,true),(9,1,true),(8,2,false),(17,2,true),(7,2,false),
      (6,1,true),(5,1,false),(14,1,true),(13,1,true),(12,1,true),
      (2,2,false),(1,1,true),(55,1,false)]
  | ⟨3,_⟩ => ![(3,2,true),(13,2,false),(21,2,true),(12,2,false),(11,2,true),
      (20,2,false),(27,2,true),(28,2,false),(34,2,true),(40,2,false),
      (45,2,false),(49,2,false),(50,2,false),(51,2,false),(48,2,true),
      (44,2,true),(38,2,false),(37,2,true),(43,2,false),(42,2,true),
      (41,2,false),(36,2,true),(35,2,false),(29,2,true),(30,2,false),
      (31,2,false),(24,2,true),(15,2,false),(14,2,true),(4,2,false)]

def loopArc (c : Colour) (i : Fin (loopLength c)) : Strand support :=
  (cell (loopData c i).1,(loopData c i).2.1)

def loopEdge (c : Colour) (i : Fin (loopLength c)) : EdgeIndex :=
  Grid.star (centres (loopData c i).1)
    (endsTable (loopData c i).1 ((loopData c i).2.1,!(loopData c i).2.2))

theorem loopEdge_present (c : Colour) (i : Fin (loopLength c)) :
    edgePresent support (loopEdge c i) := by
  unfold edgePresent
  fin_cases c <;> decide +revert

def loopContact (c : Colour) (i : Fin (loopLength c)) : Contacts support :=
  ⟨loopEdge c i,loopEdge_present c i⟩

set_option maxHeartbeats 4000000 in
def scored (c : Colour) : LoopTrace placement c where
  length := loopLength c
  arc := loopArc c
  enter i := (loopData c i).2.2
  arc_injective := by fin_cases c <;> decide
  monochromatic := by fin_cases c <;> decide
  contact := loopContact c
  joins := by fin_cases c <;> decide

theorem score_136 : score scored = 136 := by
  simp only [score,LoopTrace.tiles_card]
  decide

/-- The actual full inventory, matching sides, four closed loops and exact score. -/
theorem certificate :
    NoHoles support ∧ Inventory.UsesFullSet placement ∧
      support.card = 56 ∧ score scored = 136 :=
  ⟨no_holes,uses_full_set,card_support,score_136⟩

end Tantrix.Loops.Coloured136

namespace Tantrix.Loops
open Grid

/-- A score realized with each of the 56 physical tiles once and no holes. -/
def AttainableFullSetScore (m : ℕ) : Prop :=
  ∃ (S : Support) (P : Placement S) (R : ScoredLoops P),
    NoHoles S ∧ Inventory.UsesFullSet P ∧ score R = m

/-- Exact optimum of the stated full-set Four Longest Loops model.
The upper bound allows disconnected supports; the lower bound is coloured. -/
theorem full_set_optimum_136 :
    IsGreatest {m : ℕ | AttainableFullSetScore m} 136 := by
  refine ⟨⟨Coloured136.support,Coloured136.placement,Coloured136.scored,
    Coloured136.no_holes,Coloured136.uses_full_set,Coloured136.score_136⟩,?_⟩
  rintro m ⟨S,P,R,hn,hfull,hm⟩
  rw [← hm]
  exact score_le_136_of_no_holes R hn (Inventory.card_of_usesFullSet hfull)

end Tantrix.Loops
