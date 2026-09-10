import FullMarkedBLP.CompletionMinimum
import FullMarkedBLP.CompletionSourceBounds

namespace FullMarkedBLP

theorem realized_completion_minimum {lambda : Ordinal.{u}} {initial a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y minimum : Nat} {row : Row} {sources : List Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    (reach : ScanReach initial a rec r) (h : RankRowRealization a theta embedding)
    (hr : rowAt a r = some row) (hy : y ∈ row.marks) (hm : row.core.head? = some minimum)
    (hc : completionRecord a rec r y = some sources) :
    (completeMarkRow row y sources).core.head? = some minimum := by
  obtain ⟨k, s, xs, hk, hky, hks, ht, hb⟩ :=
    completion_sources_between historyValid h.valid reach hr hy hc
  have hmy := core_head_le_entry (h.valid r row hr) hm hky
  have hms := core_head_le_entry (h.valid r row hr) hm hks
  exact completeMarkRow_preserves_minimum (h.valid r row hr) hm hmy
    (fun x hx => hms.trans (hb x hx).1.le)

theorem realized_completion_critical {lambda : Ordinal.{u}} {initial a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y minimum : Nat} {row : Row} {sources : List Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    (reach : ScanReach initial a rec r) (h : RankRowRealization a theta embedding)
    (hr : rowAt a r = some row) (hy : y ∈ row.marks) (hm : row.core.head? = some minimum)
    (hc : completionRecord a rec r y = some sources) :
    (completeMarkRow row y sources).core.head? = some minimum ∧
      RankCriticalPoint (embedding r) (theta minimum) :=
  ⟨realized_completion_minimum historyValid reach h hr hy hm hc, h.critical r row minimum hr hm⟩

end FullMarkedBLP
