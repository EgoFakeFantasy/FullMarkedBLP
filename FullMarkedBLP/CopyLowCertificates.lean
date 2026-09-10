import FullMarkedBLP.CopyLowWord
import FullMarkedBLP.CopyLowWordCertificate
import FullMarkedBLP.CopyRowTraces
import FullMarkedBLP.MarkTraceIdentification

namespace FullMarkedBLP

/-- The literal low retention branch preserves the full natural weak
certificate. Every word and cutoff bound comes from the parent's actual
marked trace and the successful copy, without a low-tail semantic premise. -/
theorem copiedRow_low_marked {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a b : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {last row copied : Row} {p e source y x terminal minimum low : Nat} {xs : List Nat}
    (copy : shortCopy a = some b) (lastAt : rowAt a a.length = some last)
    (hp : last.p = some p) (he : last.e = some e) (hps : p ≤ source) (hse : source ≤ e)
    (minimumAt : last.core.head? = some minimum) (lowBelow : low < minimum)
    (sourceAt : rowAt a source = some row) (rowCopy : copiedRow a last source row = some copied)
    (mark : y ∈ row.marks) (targetMap : copyEntry a.length last y = some x)
    (computed : computeMarkTrace a source y = some xs)
    (terminalAt : fromRight xs 2 = some terminal) (terminalLow : terminal < p)
    (firstLow : xs.find? (· < p) = some low) :
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
  have minimumEntry : last.core[0]? = some minimum := by simpa only [List.head?_eq_getElem?] using minimumAt
  have minimumBound := core_entry_le_owner valid (List.mem_of_getElem? minimumEntry)
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
  obtain ⟨front, tail, shape, tailTrace, tailNonempty, allHigh, _, newTrace⟩ :=
    shortCopy_low_word h.valid copy lastGet hp he minimumAt lowBelow (by omega) hpn valid
      trace firstLow terminalAt terminalLow sourceMap targetMap
  have factorShape : oldWord.dropLast = front ++ tail.dropLast := by
    rw [shape, List.dropLast_append_of_ne_nil (trace_nonempty tailTrace)]
  obtain ⟨epsilon, tailCutoff⟩ := naturalCutoff_defined (fun i => rankOrdinalAction (embedding i)) theta tailNonempty
  have tailBound : epsilon ≤ theta minimum := by
    have bound := (rankRealization_trace_cutoff_bounds h tailTrace tailCutoff).2
    apply bound.trans
    by_cases same : low + 1 = minimum
    · exact (congrArg theta same).le
    · exact (h.increasing (low + 1) minimum (by omega) (by omega)).le
  have allLow : ∀ v ∈ tail.dropLast, v < a.length := by
    intro v hv
    have bound := trace_member_le_head h.valid tailTrace (List.mem_of_mem_dropLast hv)
    omega
  rw [factorShape] at cutoff certificate
  obtain ⟨newCutoff, newCertificate⟩ := shortCopy_low_natural_certificate hl h lastAt hp minimumAt hps
    front tail.dropLast allHigh allLow tailCutoff tailBound cutoff certificate
  refine ⟨k, s', front.map (fun v => v + (a.length - p)) ++ tail,
    rankOrdinalAction (rankApply hl (embedding a.length) (rankWordEmbedding embedding front)) epsilon,
    stepBound, targetAt, sourceAtCopy, newTrace, ?_, ?_⟩
  · simpa only [List.dropLast_append_of_ne_nil (trace_nonempty tailTrace)] using newCutoff
  · simpa only [List.dropLast_append_of_ne_nil (trace_nonempty tailTrace)] using newCertificate

end FullMarkedBLP
