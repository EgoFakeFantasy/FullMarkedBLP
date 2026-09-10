import FullMarkedBLP.CopyMiddleWord
import FullMarkedBLP.CopyMiddleNaturalData
import FullMarkedBLP.CopyGuardCutoff
import FullMarkedBLP.RankNaturalCutoffCardinal
import FullMarkedBLP.RankMiddleSplice
import FullMarkedBLP.CopyRowTraces
import FullMarkedBLP.MarkTraceIdentification

namespace FullMarkedBLP

/-- The actual guarded middle retention branch has its full natural weak
certificate. The original one-based guard supplies the owner cutoff bound;
the two parent marked traces supply all other bounds and limit hypotheses. -/
theorem copiedRow_middle_marked {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a b : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {last row copied : Row} {p e source y x minimum low shifted index bridgeIndex : Nat} {xs : List Nat}
    (copy : shortCopy a = some b) (lastAt : rowAt a a.length = some last)
    (hp : last.p = some p) (he : last.e = some e) (hps : p ≤ source) (hse : source ≤ e)
    (minimumAt : last.core.head? = some minimum) (lowAbove : minimum ≤ low)
    (sourceAt : rowAt a source = some row) (rowCopy : copiedRow a last source row = some copied)
    (copiedAt : rowAt b (source + (a.length - p)) = some copied)
    (mark : y ∈ row.marks) (newMark : x ∈ copied.marks)
    (markAtOld : row.core[index]? = some y) (markAtCopy : copied.core[index]? = some x)
    (targetMap : copyEntry a.length last y = some x)
    (computed : computeMarkTrace a source y = some xs) (firstLow : xs.find? (· < p) = some low)
    (lowAt : last.core[bridgeIndex]? = some low)
    (shiftedAt : last.core[bridgeIndex + last.step]? = some shifted) (bridgeMark : shifted ∈ last.marks)
    (guard : copyPositionGuard copied.core row.step index minimum = true) :
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
  have hpe := row_p_lt_e valid hp he
  have lowBelowP : low < p := by simpa using List.find?_some firstLow
  have critical := h.critical a.length last minimum lastAt minimumAt
  obtain ⟨k, s, oldWord, delta, stepBound, markAt, sourceColumnAt, trace, cutoff, certificate⟩ :=
    h.marked source row y sourceAt mark
  have sameIndex := Option.some.inj ((sorted_findIdx (h.valid source row sourceAt).1 markAt).symm.trans
    (sorted_findIdx (h.valid source row sourceAt).1 markAtOld))
  subst index
  have sameWord := computeMarkTrace_identify sourceAt (h.valid source row sourceAt).1
    ⟨row, k, s, sourceAt, mark, stepBound, markAt, sourceColumnAt, trace⟩ computed
  subst xs
  have copiedValid := shortCopy_preserves_coreValid h.valid copy _ _ copiedAt
  have copiedMarkBound := ((shortCopy_preserves_properMarks h.valid h.proper copy) _ _ copiedAt).2 x newMark
  obtain ⟨core, coreCopy, result⟩ := Option.bind_eq_some_iff.mp rowCopy
  cases Option.some.inj result
  obtain ⟨s', sourceAtCopy, sourceMap⟩ := (copiedCore_maps_entries coreCopy).at_left sourceColumnAt
  have sourceBelowCopy := copyPositionGuard_source_lt copiedValid.1 stepBound sourceAtCopy guard
  have sourceLe := copyEntry_not_below_input valid sourceMap
  have sourceBelow : s < minimum := by omega
  obtain ⟨bridgeK, bridgeSource, bridgeWord, eta, bridgeStep, bridgeTarget, bridgeSourceAt,
    bridgeTrace, bridgeCutoff, bridgeCertificate⟩ := h.marked a.length last shifted lastAt bridgeMark
  have bridgeIndexEq := Option.some.inj ((sorted_findIdx valid.1 bridgeTarget).symm.trans
    (sorted_findIdx valid.1 shiftedAt))
  have bridgeSourceAt' : last.core[bridgeIndex]? = some bridgeSource := by
    simpa only [bridgeIndexEq, Nat.add_sub_cancel] using bridgeSourceAt
  have bridgeSourceEq := Option.some.inj (bridgeSourceAt'.symm.trans lowAt)
  subst bridgeSource
  have bridgeHeadBound := ((h.proper a.length last lastAt).2 shifted bridgeMark).1
  have lowMap := copyEntry_middle_pair valid minimumAt hp he (by omega) lowAbove lowBelowP
    (by omega) lowAt shiftedAt
  have yr := (h.proper source row sourceAt).2 y mark
  obtain ⟨front, tail, shape, tailTrace, tailNonempty, allHigh, newTrace⟩ :=
    shortCopy_middle_word h.valid copy lastGet hp he minimumAt lowAbove sourceBelow (by omega) hpn valid
      trace firstLow sourceMap targetMap lowMap bridgeTrace bridgeHeadBound
  obtain ⟨epsilon, tailCutoff⟩ := naturalCutoff_defined (fun i => rankOrdinalAction (embedding i)) theta tailNonempty
  have tailBound := (rankRealization_trace_cutoff_bounds h tailTrace tailCutoff).2
  have bridgeBound : rankOrdinalAction (rankWordEmbedding embedding bridgeWord.dropLast) epsilon ≤ eta :=
    (rankOrdinalAction_monotone _ tailBound).trans
      (rankTrace_eval_successor_le_cutoff h.valid h.increasing h.edges bridgeTrace bridgeCutoff)
  have bridgeWeak : rankCutoffAgreement eta.val (embedding a.length) (rankWordEmbedding embedding bridgeWord.dropLast) := by
    intro x z hx hz
    simpa only [rankWordEmbedding_apply] using bridgeCertificate x z hx hz
  have bridgeLow : ∀ v ∈ bridgeWord.dropLast, v < a.length := by
    intro v hv
    have bound := trace_member_le_head h.valid bridgeTrace (List.mem_of_mem_dropLast hv)
    omega
  have tailLow : ∀ v ∈ tail.dropLast, v < a.length := by
    intro v hv
    have bound := trace_member_le_head h.valid tailTrace (List.mem_of_mem_dropLast hv)
    omega
  have lowLeY := trace_member_le_head h.valid trace (List.mem_of_find?_eq_some firstLow)
  have sourceBound := (rowAt_bounds sourceAt).2
  have minLeY : theta minimum ≤ theta y := by
    by_cases same : minimum = y
    · exact (congrArg theta same).le
    · exact (h.increasing minimum y (by omega) (by omega)).le
  have deltaLimit := rankCardinal_isSuccLimit_above_critical hl critical
    (minLeY.trans (rankRealization_trace_cutoff_bounds h trace cutoff).1.le)
    (rankRealization_trace_cutoff_cardinal hl h trace cutoff)
  have minLeShifted := core_head_le_entry valid minimumAt shiftedAt
  have minLeBridge : theta minimum ≤ theta shifted := by
    by_cases same : minimum = shifted
    · exact (congrArg theta same).le
    · exact (h.increasing minimum shifted (by omega) (by omega)).le
  have etaLimit := rankCardinal_isSuccLimit_above_critical hl critical
    (minLeBridge.trans (rankRealization_trace_cutoff_bounds h bridgeTrace bridgeCutoff).1.le)
    (rankRealization_trace_cutoff_cardinal hl h bridgeTrace bridgeCutoff)
  have factorShape : oldWord.dropLast = front ++ tail.dropLast := by
    rw [shape, List.dropLast_append_of_ne_nil (trace_nonempty tailTrace)]
  rw [factorShape] at cutoff certificate
  obtain ⟨newCutoff, newEmbedding, oldBound, newBridgeBound⟩ :=
    shortCopy_middle_natural_data hl h lastAt hp front bridgeWord.dropLast tail.dropLast
      allHigh bridgeLow tailLow tailCutoff cutoff bridgeWeak bridgeBound
  let newWord := front.map (fun v => v + (a.length - p)) ++ (bridgeWord.dropLast ++ tail)
  let newDelta := rankOrdinalAction (rankApply hl (embedding a.length) (rankWordEmbedding embedding front))
    (rankOrdinalAction (rankWordEmbedding embedding bridgeWord.dropLast) epsilon)
  have newFactorShape : newWord.dropLast =
      front.map (fun v => v + (a.length - p)) ++ (bridgeWord.dropLast ++ tail.dropLast) := by
    dsimp only [newWord]
    rw [List.dropLast_append_of_ne_nil (show bridgeWord.dropLast ++ tail ≠ [] from by simp [trace_nonempty tailTrace]),
      List.dropLast_append_of_ne_nil (trace_nonempty tailTrace)]
  have fullCutoff : naturalCutoff
      (fun i => rankOrdinalAction (shortCopyEmbeddingValues hl embedding a.length p i))
      (shortCopyColumnValues theta (embedding a.length) a.length p) newWord.dropLast = some newDelta := by
    rw [newFactorShape]
    exact newCutoff
  have ownerBound := shortCopy_guard_cutoff_bound hl h copy lastAt hp he minimumAt copiedAt
    (by omega : a.length ≤ source + (a.length - p)) stepBound markAtCopy copiedMarkBound.1 guard newTrace fullCutoff
  rw [shortCopyEmbeddingValues_high hl embedding hpn hps] at ownerBound
  have oldWeak : rankCutoffAgreement delta.val (embedding source)
      ((rankWordEmbedding embedding front).comp (rankWordEmbedding embedding tail.dropLast)) := by
    rw [← rankWordEmbedding_append]
    intro x z hx hz
    simpa only [rankWordEmbedding_apply] using certificate x z hx hz
  have transferred := rankApply_middle_certificate hl critical (embedding source)
    (rankWordEmbedding embedding front) (rankWordEmbedding embedding tail.dropLast)
    (rankWordEmbedding embedding bridgeWord.dropLast) deltaLimit etaLimit oldWeak bridgeWeak
    ownerBound oldBound newBridgeBound
  refine ⟨k, s', newWord, newDelta, stepBound, markAtCopy, sourceAtCopy, newTrace, fullCutoff, ?_⟩
  rw [shortCopyEmbeddingValues_high hl embedding hpn hps]
  intro x z hx hz
  rw [← rankWordEmbedding_apply, newFactorShape, newEmbedding]
  exact transferred x z hx hz

end FullMarkedBLP
