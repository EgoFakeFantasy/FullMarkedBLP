import FullMarkedBLP.CompletionExactCertificate

namespace FullMarkedBLP

/-- The actual +1 guard identifies the first propagated target for any word
length. Higher offsets require additional historical block geometry. -/
theorem completionRecord_first_propagated_target {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {rec : Records} {r y terminal last : Nat}
    {row : Row} {sources front : List Nat} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (hc : completionRecord a rec r y = some sources)
    (computed : computeMarkTrace a r y = some (front ++ [terminal, last])) :
    evalWord (fun i => rankOrdinalAction (embedding i)) front (theta (terminal + 1)) = theta (y + 1) := by
  obtain ⟨xs, _, oldComputed, _, _, _, cutoff, _⟩ := completionRecord_exact_certificate h hr hm hc
  have eq := Option.some.inj (oldComputed.symm.trans computed)
  have cut : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta
      (front ++ [terminal]) = some (theta (y + 1)) := by
    simpa [eq] using cutoff
  rw [naturalCutoff_snoc] at cut
  exact Option.some.inj cut

end FullMarkedBLP
