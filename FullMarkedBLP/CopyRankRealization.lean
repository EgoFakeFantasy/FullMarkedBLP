import FullMarkedBLP.CopyAllCertificates

namespace FullMarkedBLP

/-- Successful literal copying supplies its actual last row and parameters. -/
theorem shortCopy_parameters {a b : Pattern} (copy : shortCopy a = some b) :
    ∃ last p e, rowAt a a.length = some last ∧ last.p = some p ∧ last.e = some e := by
  unfold shortCopy at copy
  split at copy
  next => simp at copy
  next hn =>
    obtain ⟨last, lastGet, copy⟩ := Option.bind_eq_some_iff.mp copy
    obtain ⟨sources, sourcesEq, _⟩ := Option.bind_eq_some_iff.mp copy
    obtain ⟨p, e, hp, he, _, _⟩ := shortCopySources_description sourcesEq
    refine ⟨last, p, e, ?_, hp, he⟩
    simpa only [rowAt, if_neg (by omega : a.length ≠ 0), List.getLast?_eq_getElem?] using lastGet

/-- Every successful short copy preserves the full row/mark component on
the same genuine rank domain, with its concrete columns and applied owners.
There is no Sat, internal +1, packet or copied-certificate hypothesis here. -/
theorem rankRowRealization_shortCopy {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a b : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {last : Row} {p e : Nat} (copy : shortCopy a = some b)
    (lastAt : rowAt a a.length = some last) (hp : last.p = some p) (he : last.e = some e) :
    RankRowRealization b (shortCopyColumnValues theta (embedding a.length) a.length p)
      (shortCopyEmbeddingValues hl embedding a.length p) :=
  ⟨shortCopy_preserves_coreValid h.valid copy,
    shortCopy_preserves_properMarks h.valid h.proper copy,
    shortCopyColumnValues_increasing h copy lastAt hp he,
    shortCopyColumnValues_cardinals hl h copy lastAt hp he,
    shortCopy_realizes_all_edges hl h copy lastAt hp he,
    shortCopy_realizes_all_criticalPoints hl h copy lastAt hp he,
    shortCopy_all_marked hl h copy lastAt hp he⟩

theorem shortCopy_has_rankRealization {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a b : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    (copy : shortCopy a = some b) :
    ∃ (newTheta : Nat → OrdinalDomain lambda) (newEmbedding : Nat → RankElementaryEmbedding lambda),
      RankRowRealization b newTheta newEmbedding := by
  obtain ⟨last, p, e, lastAt, hp, he⟩ := shortCopy_parameters copy
  exact ⟨_, _, rankRowRealization_shortCopy hl h copy lastAt hp he⟩

end FullMarkedBLP
