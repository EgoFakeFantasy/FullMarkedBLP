import FullMarkedBLP.CopyLowWordCertificate
import FullMarkedBLP.RankPacketTransfer

namespace FullMarkedBLP

theorem rankAgreement_visible_image_le {lambda : Ordinal.{u}}
    {left right : RankElementaryEmbedding lambda} {eta : OrdinalDomain lambda}
    (agreement : rankCutoffAgreement eta.val left right) (epsilon : OrdinalDomain lambda)
    (bound : rankOrdinalAction right epsilon ≤ eta) :
    rankOrdinalAction right epsilon ≤ rankOrdinalAction left epsilon := by
  by_contra notLe
  have smaller : rankOrdinalAction left epsilon < rankOrdinalAction right epsilon := lt_of_not_ge notLe
  have visible := smaller.trans_le bound
  have same := rankAgreement_reads_visible_target agreement eta.property.le visible
    (rfl : rankOrdinalAction left epsilon = rankOrdinalAction left epsilon)
  exact (ne_of_lt smaller) same.symm

/-- Identify the mixed middle word, its exact natural cutoff, and the two
semantic comparison bounds. The remaining owner bound comes from the guard. -/
theorem shortCopy_middle_natural_data {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {last : Row} {p : Nat} (lastAt : rowAt a a.length = some last) (hp : last.p = some p)
    (front bridge tail : List Nat) (high : ∀ v ∈ front, p ≤ v)
    (bridgeLow : ∀ v ∈ bridge, v < a.length) (tailLow : ∀ v ∈ tail, v < a.length)
    {epsilon delta eta : OrdinalDomain lambda}
    (tailCutoff : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta tail = some epsilon)
    (oldCutoff : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta (front ++ tail) = some delta)
    (bridgeCertificate : rankCutoffAgreement eta.val (embedding a.length) (rankWordEmbedding embedding bridge))
    (bridgeBound : rankOrdinalAction (rankWordEmbedding embedding bridge) epsilon ≤ eta) :
    let appliedFront := rankApply hl (embedding a.length) (rankWordEmbedding embedding front)
    let newDelta := rankOrdinalAction appliedFront (rankOrdinalAction (rankWordEmbedding embedding bridge) epsilon)
    naturalCutoff (fun i => rankOrdinalAction (shortCopyEmbeddingValues hl embedding a.length p i))
      (shortCopyColumnValues theta (embedding a.length) a.length p)
      (front.map (fun v => v + (a.length - p)) ++ (bridge ++ tail)) = some newDelta ∧
    rankWordEmbedding (shortCopyEmbeddingValues hl embedding a.length p)
      (front.map (fun v => v + (a.length - p)) ++ (bridge ++ tail)) =
        appliedFront.comp ((rankWordEmbedding embedding bridge).comp (rankWordEmbedding embedding tail)) ∧
    newDelta ≤ rankOrdinalAction (embedding a.length) delta ∧
    newDelta ≤ rankOrdinalAction appliedFront eta := by
  dsimp only
  have valid := h.valid a.length last lastAt
  have hpn := fromRight_le_last valid.1 valid.2.2.1 (by omega : 0 < last.step + 1) hp
  have nonempty : tail ≠ [] := by intro same; simp [same, naturalCutoff] at tailCutoff
  have frontEmbedding :
      rankWordEmbedding (shortCopyEmbeddingValues hl embedding a.length p)
        (front.map (fun v => v + (a.length - p))) =
      rankApply hl (embedding a.length) (rankWordEmbedding embedding front) := by
    rw [rankApply_word]
    exact rankWordEmbedding_reindex _ _ _ front
      (fun v hv => shortCopyEmbeddingValues_high hl embedding hpn (high v hv))
  have tailEmbedding : rankWordEmbedding (shortCopyEmbeddingValues hl embedding a.length p) tail =
      rankWordEmbedding embedding tail := by
    simpa only [List.map_id] using rankWordEmbedding_reindex embedding
      (shortCopyEmbeddingValues hl embedding a.length p) id tail (fun v hv => if_pos (tailLow v hv))
  have bridgeEmbedding : rankWordEmbedding (shortCopyEmbeddingValues hl embedding a.length p) bridge =
      rankWordEmbedding embedding bridge := by
    simpa only [List.map_id] using rankWordEmbedding_reindex embedding
      (shortCopyEmbeddingValues hl embedding a.length p) id bridge (fun v hv => if_pos (bridgeLow v hv))
  have tailEq := naturalCutoff_reindex_eq
    (fun i => rankOrdinalAction (embedding i))
    (fun i => rankOrdinalAction (shortCopyEmbeddingValues hl embedding a.length p i))
    theta (shortCopyColumnValues theta (embedding a.length) a.length p) id tail
    (fun v hv => congrArg rankOrdinalAction (show shortCopyEmbeddingValues hl embedding a.length p (id v) = embedding v
      from if_pos (tailLow v hv)))
    (fun v hv => shortCopyColumnValues_prefix h lastAt hp (show id v + 1 ≤ a.length from by
      change v + 1 ≤ a.length
      have := tailLow v hv
      omega))
  simp only [List.map_id] at tailEq
  have newTailCutoff := tailEq.trans tailCutoff
  have oldDelta : rankOrdinalAction (rankWordEmbedding embedding front) epsilon = delta := by
    rw [naturalCutoff_append_of_nonempty _ _ front nonempty, tailCutoff, Option.map_some] at oldCutoff
    exact (rankWordEmbedding_ordinalAction embedding front epsilon).trans (Option.some.inj oldCutoff)
  refine ⟨?_, ?_, ?_, rankOrdinalAction_monotone _ bridgeBound⟩
  · rw [naturalCutoff_append_of_nonempty _ _ _ (by simp [nonempty]),
      naturalCutoff_append_of_nonempty _ _ bridge nonempty, newTailCutoff, Option.map_some, Option.map_some,
      ← rankWordEmbedding_ordinalAction, frontEmbedding,
      ← rankWordEmbedding_ordinalAction, bridgeEmbedding]
  · rw [rankWordEmbedding_append, rankWordEmbedding_append, frontEmbedding, bridgeEmbedding, tailEmbedding]
  · have compared := rankAgreement_visible_image_le bridgeCertificate epsilon bridgeBound
    have mapped := rankOrdinalAction_monotone
      (rankApply hl (embedding a.length) (rankWordEmbedding embedding front)) compared
    simpa only [rankApply_ordinal_image, oldDelta] using mapped

end FullMarkedBLP
