import Tantrix.PhysicalLoops

/-! A concrete pair of differently coloured loops sharing one tile.
The score is six, although the support contains only five cells. -/

set_option autoImplicit false
open scoped BigOperators
open Classical
noncomputable section

namespace Tantrix.Loops.Examples
open Grid

def support : Support := {(0,0),(1,0),(0,1),(-1,0),(0,-1)}

def centres : Fin 5 → Vertex := ![(0,0),(1,0),(0,1),(-1,0),(0,-1)]

def cell (k : Fin 5) : Cells support :=
  ⟨centres k, by fin_cases k <;> decide⟩

/-- For each tile: the two endpoints of red, blue, and the third strand. -/
def endsTable (k : Fin 5) (a : Fin 3 × Bool) : Side :=
  let pair := ![
    ![(3,1),(2,0),(4,5)],
    ![(0,4),(1,2),(3,5)],
    ![(5,2),(0,1),(3,4)],
    ![(0,2),(1,5),(3,4)],
    ![(0,1),(4,3),(2,5)]] k a.1
  if a.2 then pair.2 else pair.1

def inverseTable (k : Fin 5) (s : Side) : Fin 3 × Bool :=
  ![![(1,true),(0,true),(1,false),(0,false),(2,false),(2,true)],
    ![(0,false),(1,false),(1,true),(2,false),(0,true),(2,true)],
    ![(1,false),(1,true),(0,true),(2,false),(2,true),(0,false)],
    ![(0,false),(1,false),(0,true),(2,false),(2,true),(1,true)],
    ![(0,false),(0,true),(2,false),(1,true),(1,false),(2,true)]] k s

def tile (k : Fin 5) : Tile where
  ends := {
    toFun := endsTable k
    invFun := inverseTable k
    left_inv := by decide +revert
    right_inv := by decide +revert }
  colour := ⟨Fin.castSucc,Fin.castSucc_injective 3⟩

def tileAt (p : Cells support) : Tile :=
  tile (if p.val = (0,0) then 0 else if p.val = (1,0) then 1
    else if p.val = (0,1) then 2 else if p.val = (-1,0) then 3 else 4)

theorem contact_cases (e : Contacts support) :
    e.val ∈ ({(0,0,0),(1,0,0),(2,0,0),(0,-1,0),(1,0,-1),(2,-1,-1)} :
      Finset EdgeIndex) := by
  rcases e with ⟨⟨d,i,j⟩,he⟩
  fin_cases d <;>
    simp [edgePresent,edgeFirst,edgeLast,support,Prod.mk.injEq] at he ⊢ <;> omega

def placement : Placement support where
  tile := tileAt
  matching e := by
    have h := contact_cases e
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases e with ⟨e,he⟩
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [portColour,firstPort,lastPort,firstCell,lastCell,edgeFirst,edgeLast,
        tileAt,tile,inverseTable]

def redContacts (i : Fin 3) : Contacts support :=
  ⟨![(0,0,0),(2,0,0),(1,0,0)] i,
    by fin_cases i <;> simp [edgePresent,edgeFirst,edgeLast,support]⟩

def blueContacts (i : Fin 3) : Contacts support :=
  ⟨![(0,-1,0),(2,-1,-1),(1,0,-1)] i,
    by fin_cases i <;> simp [edgePresent,edgeFirst,edgeLast,support]⟩

def redArc (i : Fin 3) : Strand support := (cell (![0,1,2] i),0)
def blueArc (i : Fin 3) : Strand support := (cell (![0,3,4] i),1)

def red : LoopTrace placement 0 where
  length := 3
  arc := redArc
  enter _ := false
  arc_injective := by decide
  monochromatic := by decide
  contact := redContacts
  joins := by decide

def blue : LoopTrace placement 1 where
  length := 3
  arc := blueArc
  enter _ := false
  arc_injective := by decide
  monochromatic := by decide
  contact := blueContacts
  joins := by decide

def scored : ScoredLoops placement :=
  fun c => match c with
    | ⟨0,_⟩ => red
    | ⟨1,_⟩ => blue
    | ⟨2,_⟩ => LoopTrace.empty placement 2
    | ⟨3,_⟩ => LoopTrace.empty placement 3

theorem shared_tile : (cell 0) ∈ red.tiles ∧ (cell 0) ∈ blue.tiles := by
  constructor <;> exact Finset.mem_image.mpr ⟨(0 : Fin 3),Finset.mem_univ _,rfl⟩

theorem score_six : score scored = 6 := by
  simp only [score,LoopTrace.tiles_card]
  decide

/-- End-to-end score preservation: two three-tile loops, five distinct tiles,
six distinct selected contacts, and an even contact network. -/
theorem shared_tile_translation :
    support.card = 5 ∧ score scored = 6 ∧
      selectedCount support (network scored) = 6 ∧
      (decodeEdges support (network scored)).Even := by
  refine ⟨by decide,score_six,?_,network_even scored⟩
  rw [score_preserved,score_six]

/-- Retracing the same three strands twice is not an admissible loop trace. -/
theorem repeated_lap_rejected :
    ¬ Function.Injective (fun i : Fin 6 => redArc ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩) := by
  intro h
  have he := h (a₁ := 0) (a₂ := 3) (by decide)
  have hv := congrArg Fin.val he
  norm_num at hv

theorem empty_score :
    score (fun c => LoopTrace.empty placement c) = 0 := by
  simp [score,LoopTrace.tiles_card,LoopTrace.empty]

/-- A single open red strand cannot be passed off as a closed one-tile loop. -/
theorem open_strand_rejected :
    ¬ ((arcEnd placement (redArc 0) true = firstPort support (redContacts 0) ∧
        arcEnd placement (redArc 0) false = lastPort support (redContacts 0)) ∨
       (arcEnd placement (redArc 0) true = lastPort support (redContacts 0) ∧
        arcEnd placement (redArc 0) false = firstPort support (redContacts 0))) := by
  decide

end Tantrix.Loops.Examples
