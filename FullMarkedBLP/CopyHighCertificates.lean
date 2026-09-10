import FullMarkedBLP.CopyWordCertificates
import FullMarkedBLP.CopyHighWord
import FullMarkedBLP.MarkTraceIdentification

namespace FullMarkedBLP

/-- The literal high retention branch preserves the complete marked-row
certificate, with its actual trace word and exact natural cutoff. -/
theorem copiedRow_high_marked {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a b : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {last row copied : Row} {p e source y x terminal : Nat} {xs : List Nat}
    (copy : shortCopy a = some b) (lastAt : rowAt a a.length = some last)
    (hp : last.p = some p) (he : last.e = some e) (hps : p ≤ source) (hse : source ≤ e)
    (sourceAt : rowAt a source = some row) (rowCopy : copiedRow a last source row = some copied)
    (mark : y ∈ row.marks) (targetMap : copyEntry a.length last y = some x)
    (computed : computeMarkTrace a source y = some xs)
    (terminalAt : fromRight xs 2 = some terminal) (high : p ≤ terminal) :
    ∃ k s word delta, copied.step ≤ k ∧ copied.core[k]? = some x ∧
      copied.core[k - copied.step]? = some s ∧ Trace b s x word ∧
      naturalCutoff (fun i => rankOrdinalAction (shortCopyEmbeddingValues hl embedding a.length p i))
        (shortCopyColumnValues theta (embedding a.length) a.length p) word.dropLast = some delta ∧
      rankCutoffAgreement delta.val
        (shortCopyEmbeddingValues hl embedding a.length p (source + (a.length - p)))
        (evalWord (fun i => (shortCopyEmbeddingValues hl embedding a.length p i :
          RankDomain lambda → RankDomain lambda)) word.dropLast) := by
  have hn : a.length ≠ 0 := Nat.ne_of_gt (rowAt_bounds lastAt).1
  have lastGet : a.getLast? = some last := by
    simpa only [rowAt, if_neg hn, List.getLast?_eq_getElem?] using lastAt
  have valid := h.valid a.length last lastAt
  have hpn := fromRight_le_last valid.1 valid.2.2.1 (by omega : 0 < last.step + 1) hp
  obtain ⟨k, s, oldWord, delta, stepBound, markAt, sourceColumnAt, trace, cutoff, certificate⟩ :=
    h.marked source row y sourceAt mark
  have sameWord := computeMarkTrace_identify sourceAt (h.valid source row sourceAt).1
    ⟨row, k, s, sourceAt, mark, stepBound, markAt, sourceColumnAt, trace⟩ computed
  subst xs
  obtain ⟨core, coreCopy, result⟩ := Option.bind_eq_some_iff.mp rowCopy
  cases Option.some.inj result
  obtain ⟨target, targetAt, targetCopy⟩ := (copiedCore_maps_entries coreCopy).at_left markAt
  have sameTarget := Option.some.inj (targetCopy.symm.trans targetMap)
  subst target
  obtain ⟨s', sourceAtCopy, sourceMap⟩ := (copiedCore_maps_entries coreCopy).at_left sourceColumnAt
  have yr := (h.proper source row sourceAt).2 y mark
  have newTrace := shortCopy_high_terminal_word h.valid copy lastGet hp he high (by omega)
    hpn valid trace terminalAt sourceMap targetMap
  have allHigh : ∀ v ∈ oldWord.dropLast, p ≤ v := by
    intro v hv
    have bound := trace_factor_ge_terminal h.valid trace terminalAt hv
    omega
  obtain ⟨newCutoff, newCertificate⟩ := shortCopy_high_natural_certificate hl theta embedding
    hpn hps oldWord.dropLast allHigh cutoff certificate
  refine ⟨k, s', oldWord.dropLast.map (fun v => v + (a.length - p)) ++ [s'],
    rankOrdinalAction (embedding a.length) delta, stepBound, targetAt, sourceAtCopy, newTrace, ?_, ?_⟩
  · simpa only [List.dropLast_concat] using newCutoff
  · simpa only [List.dropLast_concat] using newCertificate

end FullMarkedBLP
