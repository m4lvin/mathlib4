import Mathlib.Data.MLList.BestFirst
import Mathlib.Data.Nat.Sqrt

/-!
# Testing best first search and beam search.

We check that `bestFirstSearch` can find its way around a wall.
-/

open Lean MLList Function

def Point := Int × Int
deriving Repr

def wall : Point → Bool :=
  fun ⟨x, y⟩ => x ≤ 3 || y ≤ 3 || x ≥ 20 || y ≥ 20 || (x ≥ 6 && y ≥ 6)

def nbhd : Point → MLList MetaM Point :=
  fun ⟨x, y⟩ => MLList.ofList
      ([(x+1,y), (x-1,y), (x,y+1), (x,y-1)].filter wall)

def emb : Point → Nat ×ₗ (Int ×ₗ Int)
  | (x, y) => (x.natAbs^2 + y.natAbs^2, x, y)

lemma emb_injective : Injective emb :=
  fun ⟨x, y⟩ ⟨w, z⟩ h => by injection h

instance : LinearOrder Point := LinearOrder.lift' _ emb_injective

/-- info: -/
#guard_msgs in
#eval do guard <|
  (← (bestFirstSearch nbhd (10, 10) (maxQueued := some 4) |>.takeUpToFirst (· = (0,0))).force) =
  [(10, 10), (11, 10), (9, 10), (8, 10), (7, 10), (6, 10), (6, 11), (6, 9), (7, 9), (6, 8), (7, 8),
   (6, 7), (7, 7), (6, 6), (7, 6), (8, 6), (8, 7), (9, 6), (9, 7), (8, 8), (10, 6), (9, 8), (8, 9),
   (10, 7), (11, 6), (9, 9), (11, 7), (10, 8), (12, 6), (10, 9), (11, 8), (13, 6), (12, 7), (11, 9),
   (12, 8), (13, 7), (12, 9), (13, 8), (14, 7), (13, 9), (12, 10), (14, 8), (13, 10), (12, 11),
   (15, 7), (14, 6), (15, 6), (15, 8), (14, 9), (16, 6), (15, 9), (14, 10), (16, 8), (17, 6),
   (16, 7), (15, 10), (14, 11), (17, 7), (15, 11), (13, 11), (13, 12), (14, 12), (12, 12), (11, 12),
   (10, 12), (9, 12), (8, 12), (7, 12), (6, 12), (6, 13), (7, 13), (7, 11), (8, 11), (9, 11),
   (10, 11), (6, 14), (11, 11), (7, 14), (6, 15), (8, 14), (7, 15), (9, 14), (8, 15), (8, 13),
   (9, 13), (10, 13), (6, 16), (11, 13), (10, 14), (12, 13), (11, 14), (7, 16), (6, 17), (10, 15),
   (8, 16), (7, 17), (9, 16), (8, 17), (6, 18), (10, 16), (9, 17), (9, 15), (8, 18), (11, 16),
   (10, 17), (12, 16), (11, 17), (11, 15), (12, 15), (13, 15), (12, 14), (13, 14), (14, 14),
   (13, 13), (14, 13), (15, 13), (16, 13), (15, 14), (15, 12), (16, 12), (17, 12), (16, 11),
   (17, 11), (16, 10), (17, 10), (16, 9), (17, 9), (18, 9), (17, 8), (18, 8), (19, 8), (18, 7),
   (19, 7), (18, 6), (19, 6), (20, 6), (21, 6), (20, 7), (20, 5), (21, 5), (20, 4), (21, 4),
   (20, 3), (21, 3), (19, 3), (18, 3), (17, 3), (16, 3), (15, 3), (14, 3), (13, 3), (12, 3),
   (11, 3), (10, 3), (9, 3), (8, 3), (7, 3), (6, 3), (5, 3), (4, 3), (3, 3), (2, 3), (1, 3),
   (0, 3), (-1, 3),  (0, 4),  (0, 2),  (1, 2),  (-1, 2),  (0, 1),  (1, 1),  (-1, 1),  (0, 0)]
