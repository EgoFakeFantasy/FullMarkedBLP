import FullMarkedBLP.CompleteMarkHistoricalTrace

namespace FullMarkedBLP

/-- Local semantic obligations at one actual frozen-mark event. -/
def CompletionEventGeometry {lambda : Ordinal.{u}} (a : Pattern) (rec : Records) (r y : Nat)
    (theta : Nat → OrdinalDomain lambda) (embedding : Nat → RankElementaryEmbedding lambda) : Prop :=
  RankRowRealization a theta embedding ∧
  ∀ row sources, rowAt a r = some row → completionRecord a rec r y = some sources →
    ∃ k p nextTarget, row.p = some p ∧ row.step ≤ k ∧ row.core[k]? = some y ∧
      (row.full r)[k + 1]? = some nextTarget ∧ sources.Nodup ∧
      (∀ x ∈ sources, x ≤ a.length + 1) ∧ y + sources.length < nextTarget ∧
      y + sources.length < r ∧
      ∀ x ∈ sources, rankOrdinalAction (embedding r) (theta x) =
        theta (y + 1 + (sources.filter (· < x)).length)

/-- The old word survives the entire frozen fold once the local obligations
are established at each actual processed state. This does not establish them. -/
theorem frozen_fold_preserves_historical_trace {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r z : Nat} {xs : List Nat} (frozen : List Nat)
    (events : ∀ processed y suffix, frozen = processed ++ y :: suffix →
      CompletionEventGeometry
        (processed.foldl (fun current mark => completeMark current rec r mark) a) rec r y theta embedding)
    (old : MarkTrace a r z xs) :
    MarkTrace (frozen.foldl (fun current mark => completeMark current rec r mark) a) r z xs := by
  induction frozen generalizing a with
  | nil => exact old
  | cons y rest ih =>
    have localEvent := events [] y rest rfl
    have preserved := completeMark_preserves_historical_trace localEvent.1 localEvent.2 old
    simp only [List.foldl_cons]
    apply ih _ preserved
    intro processed next suffix he
    have event := events (y :: processed) next suffix (by simp only [List.cons_append, he])
    simpa only [List.foldl_cons] using event

end FullMarkedBLP

