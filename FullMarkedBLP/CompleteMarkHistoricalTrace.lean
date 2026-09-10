import FullMarkedBLP.CompletionSemanticMarks

namespace FullMarkedBLP

/-- Actual completeMark preserves a supplied historical word when every
successful record supplies the local semantic packet and gap witnesses. -/
theorem completeMark_preserves_historical_trace {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {rec : Records} {r y z : Nat} {xs : List Nat}
    (localPacket : ∀ row sources, rowAt a r = some row →
      completionRecord a rec r y = some sources →
      ∃ k p nextTarget, row.p = some p ∧ row.step ≤ k ∧ row.core[k]? = some y ∧
        (row.full r)[k + 1]? = some nextTarget ∧ sources.Nodup ∧
        (∀ x ∈ sources, x ≤ a.length + 1) ∧ y + sources.length < nextTarget ∧
        y + sources.length < r ∧
        ∀ x ∈ sources, rankOrdinalAction (embedding r) (theta x) =
          theta (y + 1 + (sources.filter (· < x)).length))
    (old : MarkTrace a r z xs) : MarkTrace (completeMark a rec r y) r z xs := by
  obtain ⟨row, k, s, hr, hm, hk, hky, hks, trace⟩ := old
  have old : MarkTrace a r z xs := ⟨row, k, s, hr, hm, hk, hky, hks, trace⟩
  cases hc : completionRecord a rec r y with
  | none => simpa only [completeMark, hr, hc] using old
  | some sources =>
    obtain ⟨j, p, nextTarget, hp, hj, hjy, hnext, hs, bounds, gap, beforeOwner, packet⟩ :=
      localPacket row sources hr hc
    have result := rankRealization_completion_preserves_markTrace h hr hp hj hjy hnext
      hs bounds gap beforeOwner packet old
    simpa only [completeMark, hr, hc] using result

end FullMarkedBLP
