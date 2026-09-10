import FullMarkedBLP.CurrentExactCutoff

namespace FullMarkedBLP

theorem completionRecord_exact_certificate {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {rec : Records} {r y : Nat}
    {row : Row} {sources : List Nat} (hr : rowAt a r = some row) (hy : y ∈ row.marks)
    (hc : completionRecord a rec r y = some sources) :
    ∃ xs terminal, computeMarkTrace a r y = some xs ∧ MarkTrace a r y xs ∧
      fromRight xs 2 = some terminal ∧ recordAt rec terminal = some sources ∧
      naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some (theta (y + 1)) ∧
      rankCutoffAgreement (theta (y + 1)).val (embedding r)
        (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
  obtain ⟨xs, terminal, hx, hf, hrrec, _, hg⟩ := completionRecord_iff.mp hc
  obtain ⟨k, s, ys, delta, hk, hky, hks, ht, hd, hw⟩ := h.marked r row y hr hy
  have hm : MarkTrace a r y ys := ⟨row, k, s, hr, hy, hk, hky, hks, ht⟩
  have he := Option.some.inj (hx.symm.trans (computeMarkTrace_complete h.valid hm))
  subst xs
  have hdelta := currentPlusOne_trace_cutoff h ht hg hd
  subst delta
  exact ⟨ys, terminal, hx, hm, hf, hrrec, hd, hw⟩

end FullMarkedBLP
