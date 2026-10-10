import Tantrix.GeometryApplication
import Mathlib.Data.Fin.VecNotation

/-!
# Coloured tile loops and their contact network

Each tile pairs its six sides into three differently coloured strands.
A loop is traced once around a finite cyclic sequence of distinct strands;
every exit is glued to the next entry along a genuine lattice contact.
No evenness or score identity is assumed. Empty traces permit a missing colour.
The exact 56-tile inventory is deliberately not needed for this upper bound.
-/

set_option autoImplicit false
open scoped BigOperators
open Classical
noncomputable section

namespace Tantrix.Loops
open Grid

abbrev Colour := Fin 4
abbrev Side := Fin 6
abbrev Strand (S : Support) := Cells S × Fin 3
abbrev Port (S : Support) := Cells S × Side

/-- The two ends of each of three differently coloured tile strands.
Rotations and every pairing shape are allowed; the actual inventory is a subset. -/
structure Tile where
  ends : (Fin 3 × Bool) ≃ Side
  colour : Fin 3 ↪ Colour

def portColour {S : Support} (tiles : Cells S → Tile) (p : Port S) : Colour :=
  (tiles p.1).colour ((tiles p.1).ends.symm p.2).1

/-- Side order follows Grid.star: west, east, south, north, northwest, southeast. -/
def firstPort (S : Support) (e : Contacts S) : Port S :=
  (firstCell S e, ![1,3,4] e.val.1)

def lastPort (S : Support) (e : Contacts S) : Port S :=
  (lastCell S e, ![0,2,5] e.val.1)

/-- The side indexing really uses the same contact as the existing grid model. -/
theorem ports_use_contact (S : Support) (e : Contacts S) :
    star (firstPort S e).1.val (firstPort S e).2 = e.val ∧
    star (lastPort S e).1.val (lastPort S e).2 = e.val := by
  rcases e with ⟨⟨d,i,j⟩,he⟩
  fin_cases d <;> simp [firstPort,lastPort,firstCell,lastCell,edgeFirst,edgeLast,Grid.star]

structure Placement (S : Support) where
  tile : Cells S → Tile
  matching : ∀ e : Contacts S,
    portColour tile (firstPort S e) = portColour tile (lastPort S e)

def arcEnd {S : Support} (P : Placement S) (a : Strand S) (b : Bool) : Port S :=
  (a.1, (P.tile a.1).ends (a.2,b))

theorem arcEnd_injective {S : Support} (P : Placement S) :
    Function.Injective (fun ab : Strand S × Bool => arcEnd P ab.1 ab.2) := by
  rintro ⟨⟨p,a⟩,b⟩ ⟨⟨q,c⟩,d⟩ h
  have hp : p = q := congrArg Prod.fst h
  subst q
  have hs := (P.tile p).ends.injective (congrArg Prod.snd h)
  have ha : a = c := congrArg Prod.fst hs
  have hb : b = d := congrArg Prod.snd hs
  subst c; subst d
  rfl

@[simp] theorem arcEnd_colour {S : Support} (P : Placement S) (a : Strand S) (b : Bool) :
    portColour P.tile (arcEnd P a b) = (P.tile a.1).colour a.2 := by
  simp [portColour,arcEnd]

/-- One closed monochromatic loop traversed once, or an empty trace.
Distinct strands prevent traversing a loop twice to inflate its score.
The joining equations implement following an arc and crossing a matching side. -/
structure LoopTrace {S : Support} (P : Placement S) (c : Colour) where
  length : ℕ
  arc : Fin length → Strand S
  enter : Fin length → Bool
  arc_injective : Function.Injective arc
  monochromatic : ∀ i, (P.tile (arc i).1).colour (arc i).2 = c
  contact : Fin length → Contacts S
  joins : ∀ i,
    (arcEnd P (arc i) (!(enter i)) = firstPort S (contact i) ∧
      arcEnd P (arc (finRotate length i)) (enter (finRotate length i)) =
        lastPort S (contact i)) ∨
    (arcEnd P (arc i) (!(enter i)) = lastPort S (contact i) ∧
      arcEnd P (arc (finRotate length i)) (enter (finRotate length i)) =
        firstPort S (contact i))

namespace LoopTrace
variable {S : Support} {P : Placement S} {c : Colour} (L : LoopTrace P c)

/-- An absent loop contributes no strands, contacts or tiles. -/
def empty (P : Placement S) (c : Colour) : LoopTrace P c where
  length := 0
  arc := Fin.elim0
  enter := Fin.elim0
  arc_injective := fun i => Fin.elim0 i
  monochromatic i := Fin.elim0 i
  contact := Fin.elim0
  joins i := Fin.elim0 i

def incoming (i : Fin L.length) : Port S := arcEnd P (L.arc i) (L.enter i)
def outgoing (i : Fin L.length) : Port S := arcEnd P (L.arc i) (!(L.enter i))

theorem outgoing_injective : Function.Injective L.outgoing := by
  intro i j h
  exact L.arc_injective (congrArg Prod.fst
    (@arcEnd_injective S P (L.arc i,!(L.enter i)) (L.arc j,!(L.enter j)) h))

theorem outgoing_ne_incoming (i j : Fin L.length) : L.outgoing i ≠ L.incoming j := by
  intro h
  have he := @arcEnd_injective S P (L.arc i,!(L.enter i)) (L.arc j,L.enter j) h
  have hij := L.arc_injective (congrArg Prod.fst he)
  subst j
  have hb := congrArg Prod.snd he
  cases L.enter i <;> simp at hb

/-- Non-repetition of contacts follows from genuine paired strands, not a hypothesis. -/
theorem contact_injective : Function.Injective L.contact := by
  intro i j he
  have hi := L.joins i
  have hj := L.joins j
  rw [he] at hi
  rcases hi with ⟨hi,hi'⟩ | ⟨hi,hi'⟩ <;>
    rcases hj with ⟨hj,hj'⟩ | ⟨hj,hj'⟩
  · exact L.outgoing_injective (hi.trans hj.symm)
  · exact (L.outgoing_ne_incoming i _ (hi.trans hj'.symm)).elim
  · exact (L.outgoing_ne_incoming i _ (hi.trans hj'.symm)).elim
  · exact L.outgoing_injective (hi.trans hj.symm)

theorem contact_colour (i : Fin L.length) :
    portColour P.tile (firstPort S (L.contact i)) = c := by
  rcases L.joins i with ⟨h,_⟩ | ⟨h,_⟩
  · rw [← h,arcEnd_colour]
    exact L.monochromatic i
  · rw [P.matching,← h,arcEnd_colour]
    exact L.monochromatic i

/-- A monochromatic trace visits a tile at most once: a tile has only one
strand of each colour. Other colours may visit that same tile. -/
theorem tiles_injective : Function.Injective (fun i => (L.arc i).1) := by
  intro i j hp
  change (L.arc i).1 = (L.arc j).1 at hp
  have hcol := (L.monochromatic i).trans (L.monochromatic j).symm
  rw [hp] at hcol
  have ha := (P.tile (L.arc j).1).colour.injective hcol
  exact L.arc_injective (Prod.ext hp ha)

def tiles : Finset (Cells S) := Finset.univ.image (fun i => (L.arc i).1)

theorem tiles_card : L.tiles.card = L.length := by
  rw [tiles,Finset.card_image_of_injective _ L.tiles_injective]
  simp

theorem contact_incidence (i : Fin L.length) (p : Cells S) :
    incidence S (L.contact i) p =
      (if (L.arc i).1 = p then (1 : Bit) else 0) +
      (if (L.arc (finRotate L.length i)).1 = p then 1 else 0) := by
  rcases L.joins i with ⟨h1,h2⟩ | ⟨h1,h2⟩
  all_goals
    have hfirst := congrArg Prod.fst h1
    have hlast := congrArg Prod.fst h2
    simp only [arcEnd,firstPort,lastPort] at hfirst hlast
    simp [incidence,FiniteGraph.incidence,← hfirst,← hlast,add_comm]

/-- Entries and exits cancel modulo two around the closed cyclic trace. -/
theorem incidence_sum (p : Cells S) :
    ∑ i, incidence S (L.contact i) p = 0 := by
  simp_rw [L.contact_incidence]
  rw [Finset.sum_add_distrib,
    Equiv.sum_comp (finRotate L.length) (fun i => if (L.arc i).1 = p then (1 : Bit) else 0)]
  exact bit_self _

end LoopTrace

variable {S : Support} {P : Placement S}

/-- At most one traced loop of each colour; an absent loop has length zero.
No longest-loop hypothesis is needed because the bound holds for every choice. -/
abbrev ScoredLoops (P : Placement S) := (c : Colour) → LoopTrace P c

abbrev Occurrence (R : ScoredLoops P) := (c : Colour) × Fin (R c).length

def usedContact (R : ScoredLoops P) (i : Occurrence R) : Contacts S :=
  (R i.1).contact i.2

/-- Distinct colours cannot share a contact, even when they share a tile. -/
theorem usedContact_injective (R : ScoredLoops P) : Function.Injective (usedContact R) := by
  rintro ⟨c,i⟩ ⟨d,j⟩ h
  have hc := (R c).contact_colour i
  have hd := (R d).contact_colour j
  change (R c).contact i = (R d).contact j at h
  rw [h] at hc
  have hcd : c = d := hc.symm.trans hd
  subst d
  exact Sigma.ext rfl (heq_of_eq ((R c).contact_injective h))

def contactSet (R : ScoredLoops P) : Finset (Contacts S) :=
  Finset.univ.image (usedContact R)

def network (R : ScoredLoops P) (e : Contacts S) : Bit :=
  ∑ i : Occurrence R, if usedContact R i = e then 1 else 0

/-- Score counts the tiles on each colour's loop separately. -/
def score (R : ScoredLoops P) : ℕ := ∑ c, (R c).tiles.card

theorem network_indicator (R : ScoredLoops P) (e : Contacts S) :
    network R e = if e ∈ contactSet R then 1 else 0 := by
  by_cases he : e ∈ contactSet R
  · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp he
    rw [network,Finset.sum_eq_single i]
    · simp [hi,he]
    · intro j _ hji
      have hne : usedContact R j ≠ e := fun h => hji (usedContact_injective R (h.trans hi.symm))
      simp [hne]
    · simp
  · have hn : ∀ i, usedContact R i ≠ e := by
      intro i hi
      exact he (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩)
    simp [network,hn,he]

theorem score_preserved (R : ScoredLoops P) :
    selectedCount S (network R) = score R := by
  have hc : (contactSet R).card = score R := by
    rw [contactSet,Finset.card_image_of_injective _ (usedContact_injective R)]
    simp [score,LoopTrace.tiles_card,Fintype.card_sigma]
  simpa [selectedCount,network_indicator] using hc

theorem network_even (R : ScoredLoops P) : (decodeEdges S (network R)).Even := by
  apply (decode_even_iff S _).mpr
  funext p
  change (∑ e, incidence S e p * network R e) = 0
  simp only [network,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [Fintype.sum_sigma]
  apply Finset.sum_eq_zero
  intro c _
  exact (R c).incidence_sum p

/-- The translation derives both parity and exact score from paired tile strands. -/
theorem to_even_network (R : ScoredLoops P) :
    (decodeEdges S (network R)).Even ∧ selectedCount S (network R) = score R :=
  ⟨network_even R,score_preserved R⟩

/-- In particular this covers choosing the longest closed loop of each colour. -/
theorem score_le_136 (R : ScoredLoops P)
    (hc : Connected S) (hn : NoHoles S) (h56 : S.card = 56) : score R ≤ 136 := by
  rw [← score_preserved R]
  exact Grid.score_le_136 S hc hn h56 (network R) (network_even R)

end Tantrix.Loops
