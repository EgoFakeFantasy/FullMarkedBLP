import FullMarkedBLP.ScanRankReach

namespace FullMarkedBLP

/-- Local geometric obligations for events strictly preceding a cursor. -/
def ScanPriorGeometry {lambda : Ordinal.{u}} (initial : Pattern)
    (initialTheta : Nat → OrdinalDomain lambda)
    (initialEmbedding : Nat → RankElementaryEmbedding lambda) (cursor : Nat) : Prop :=
  ∀ before history owner oldTheta oldEmbedding,
    ScanRankReach initial initialTheta initialEmbedding before history owner oldTheta oldEmbedding →
    owner < cursor →
    (∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i) ∧
    (∀ i, predecessor (completeFrozenMarks before history owner) i = predecessor before i)

theorem scanPriorGeometry_mono {lambda : Ordinal.{u}} {initial : Pattern}
    {initialTheta : Nat → OrdinalDomain lambda}
    {initialEmbedding : Nat → RankElementaryEmbedding lambda} {earlier later : Nat}
    (h : ScanPriorGeometry initial initialTheta initialEmbedding later) (hle : earlier ≤ later) :
    ScanPriorGeometry initial initialTheta initialEmbedding earlier := by
  intro before history owner oldTheta oldEmbedding reach hb
  exact h before history owner oldTheta oldEmbedding reach (by omega)

end FullMarkedBLP
