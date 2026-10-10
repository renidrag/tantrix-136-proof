import Tantrix.PhysicalLoops

/-!
# The 56 numbered Tantrix tiles

The clockwise six-side colour words are transcribed from Jaap Scherphuis's
number-conversion table, in current tile-number order 1 through 56:
https://www.jaapsch.net/puzzles/tantrix.htm

Colours: red = 0, blue = 1, green = 2, yellow = 3.
Rotations are allowed; reflection of an individual tile is not.
The full-set predicate requires a bijection with these 56 inventory entries.
-/

set_option autoImplicit false

namespace Tantrix.Loops.Inventory
open Grid

/-- Clockwise sides in the paired-side grid convention. -/
def clockwiseSide : Fin 6 → Side := ![1,3,4,0,2,5]

theorem clockwiseSide_bijective : Function.Bijective clockwiseSide := by decide

/-- Current numbered inventory; row k is physical tile k+1.
The comment preserves the source's clockwise colour word. -/
def pattern : Fin 56 → Fin 6 → Colour := ![
  ![3,3,1,0,1,0], -- 1: YYBRBR
  ![0,0,1,3,3,1], -- 2: RRBYYB
  ![1,1,3,3,0,0], -- 3: BBYYRR
  ![1,0,3,1,3,0], -- 4: BRYBYR
  ![1,1,0,3,3,0], -- 5: BBRYYR
  ![3,1,0,3,0,1], -- 6: YBRYRB
  ![1,1,3,0,3,0], -- 7: BBYRYR
  ![1,1,0,3,0,3], -- 8: BBRYRY
  ![0,1,3,0,3,1], -- 9: RBYRYB
  ![3,3,0,1,0,1], -- 10: YYRBRB
  ![0,0,1,3,1,3], -- 11: RRBYBY
  ![0,0,3,1,3,1], -- 12: RRYBYB
  ![1,1,3,0,0,3], -- 13: BBYRRY
  ![1,1,0,0,3,3], -- 14: BBRRYY
  ![2,2,0,3,3,0], -- 15: GGRYYR
  ![2,2,3,0,0,3], -- 16: GGYRRY
  ![3,3,2,0,2,0], -- 17: YYGRGR
  ![3,3,0,2,0,2], -- 18: YYRGRG
  ![0,0,2,3,2,3], -- 19: RRGYGY
  ![0,0,3,2,3,2], -- 20: RRYGYG
  ![2,2,0,0,3,3], -- 21: GGRRYY
  ![0,0,2,3,3,2], -- 22: RRGYYG
  ![2,2,3,3,0,0], -- 23: GGYYRR
  ![2,2,1,0,0,1], -- 24: GGBRRB
  ![1,1,2,2,0,0], -- 25: BBGGRR
  ![1,1,2,0,0,2], -- 26: BBGRRG
  ![0,0,1,2,1,2], -- 27: RRBGBG
  ![1,1,0,0,2,2], -- 28: BBRRGG
  ![0,0,2,1,2,1], -- 29: RRGBGB
  ![1,1,0,2,2,0], -- 30: BBRGGR
  ![2,2,0,3,0,3], -- 31: GGRYRY
  ![2,0,3,2,3,0], -- 32: GRYGYR
  ![2,2,3,0,3,0], -- 33: GGYRYR
  ![0,2,3,0,3,2], -- 34: RGYRYG
  ![3,2,0,3,0,2], -- 35: YGRYRG
  ![2,2,0,1,0,1], -- 36: GGRBRB
  ![1,1,2,0,2,0], -- 37: BBGRGR
  ![1,1,0,2,0,2], -- 38: BBRGRG
  ![2,1,0,2,0,1], -- 39: GBRGRB
  ![1,2,0,1,0,2], -- 40: BGRBRG
  ![2,2,1,0,1,0], -- 41: GGBRBR
  ![0,1,2,0,2,1], -- 42: RBGRGB
  ![1,1,3,3,2,2], -- 43: BBYYGG
  ![3,1,2,3,2,1], -- 44: YBGYGB
  ![1,1,2,2,3,3], -- 45: BBGGYY
  ![2,2,1,3,1,3], -- 46: GGBYBY
  ![1,1,3,2,2,3], -- 47: BBYGGY
  ![2,2,1,3,3,1], -- 48: GGBYYB
  ![1,1,2,3,3,2], -- 49: BBGYYG
  ![1,2,3,1,3,2], -- 50: BGYBYG
  ![2,1,3,2,3,1], -- 51: GBYGYB
  ![2,2,3,1,3,1], -- 52: GGYBYB
  ![3,3,2,1,2,1], -- 53: YYGBGB
  ![3,3,1,2,1,2], -- 54: YYBGBG
  ![1,1,2,3,2,3], -- 55: BBGYGY
  ![1,1,3,2,3,2] -- 56: BBYGYG
]

/-- A placement uses each numbered physical tile exactly once, with an
independent rotation and the same colour at every corresponding side. -/
def UsesFullSet {S : Support} (P : Placement S) : Prop :=
  ∃ assignment : Cells S ≃ Fin 56, ∃ rotation : Cells S → Fin 6,
    ∀ p d, portColour P.tile (p,clockwiseSide d) =
      pattern (assignment p) (d + rotation p)

theorem card_of_usesFullSet {S : Support} {P : Placement S}
    (h : UsesFullSet P) : S.card = 56 := by
  obtain ⟨assignment,_,_⟩ := h
  simpa using Fintype.card_congr assignment

end Tantrix.Loops.Inventory
