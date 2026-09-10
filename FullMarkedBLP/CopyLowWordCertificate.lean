import FullMarkedBLP.CopySemanticValues
import FullMarkedBLP.RankWordConcatenation
import FullMarkedBLP.NaturalCutoffReindexExact
import FullMarkedBLP.RankApplicationLowTail

namespace FullMarkedBLP

/-- An identified high-prefix/low-tail word carries the actual copied
natural cutoff. The supplied tail bound is discharged from trace geometry
by the concrete low-branch theorem. -/
theorem shortCopy_low_natural_certificate {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {last : Row} {p source minimum : Nat} (lastAt : rowAt a a.length = some last)
    (hp : last.p = some p) (minimumAt : last.core.head? = some minimum) (hps : p ≤ source)
    (front tail : List Nat) (high : ∀ v ∈ front, p ≤ v) (low : ∀ v ∈ tail, v < a.length)
    {epsilon delta : OrdinalDomain lambda}
    (tailCutoff : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta tail = some epsilon)
    (tailBound : epsilon ≤ theta minimum)
    (cutoff : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta (front ++ tail) = some delta)
    (certificate : rankCutoffAgreement delta.val (embedding source)
      (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) (front ++ tail))) :
    let newDelta := rankOrdinalAction (rankApply hl (embedding a.length) (rankWordEmbedding embedding front)) epsilon
    naturalCutoff (fun i => rankOrdinalAction (shortCopyEmbeddingValues hl embedding a.length p i))
      (shortCopyColumnValues theta (embedding a.length) a.length p)
      (front.map (fun v => v + (a.length - p)) ++ tail) = some newDelta ∧
    rankCutoffAgreement newDelta.val
      (shortCopyEmbeddingValues hl embedding a.length p (source + (a.length - p)))
      (evalWord (fun i => (shortCopyEmbeddingValues hl embedding a.length p i :
        RankDomain lambda → RankDomain lambda)) (front.map (fun v => v + (a.length - p)) ++ tail)) := by
  dsimp only
  have valid := h.valid a.length last lastAt
  have hpn := fromRight_le_last valid.1 valid.2.2.1 (by omega : 0 < last.step + 1) hp
  have nonempty : tail ≠ [] := by intro same; simp [same, naturalCutoff] at tailCutoff
  have frontFactors : ∀ v ∈ front,
      shortCopyEmbeddingValues hl embedding a.length p (v + (a.length - p)) =
        rankApply hl (embedding a.length) (embedding v) :=
    fun v hv => shortCopyEmbeddingValues_high hl embedding hpn (high v hv)
  have frontEmbedding :
      rankWordEmbedding (shortCopyEmbeddingValues hl embedding a.length p)
        (front.map (fun v => v + (a.length - p))) =
      rankApply hl (embedding a.length) (rankWordEmbedding embedding front) := by
    rw [rankApply_word]
    exact rankWordEmbedding_reindex _ _ _ front frontFactors
  have tailFactors : ∀ v ∈ tail,
      shortCopyEmbeddingValues hl embedding a.length p (id v) = embedding v :=
    fun v hv => if_pos (low v hv)
  have tailEmbedding : rankWordEmbedding (shortCopyEmbeddingValues hl embedding a.length p) tail =
      rankWordEmbedding embedding tail := by
    simpa only [List.map_id] using rankWordEmbedding_reindex _ _ id tail tailFactors
  have tailSuccessors : ∀ v ∈ tail,
      shortCopyColumnValues theta (embedding a.length) a.length p (id v + 1) = theta (v + 1) := by
    intro v hv
    change shortCopyColumnValues theta (embedding a.length) a.length p (v + 1) = theta (v + 1)
    exact shortCopyColumnValues_prefix h lastAt hp (by have := low v hv; omega)
  have tailEq := naturalCutoff_reindex_eq
    (fun i => rankOrdinalAction (embedding i))
    (fun i => rankOrdinalAction (shortCopyEmbeddingValues hl embedding a.length p i))
    theta (shortCopyColumnValues theta (embedding a.length) a.length p) id tail
    (fun v hv => congrArg rankOrdinalAction (tailFactors v hv)) tailSuccessors
  simp only [List.map_id] at tailEq
  have newTailCutoff := tailEq.trans tailCutoff
  have oldDelta : rankOrdinalAction (rankWordEmbedding embedding front) epsilon = delta := by
    rw [naturalCutoff_append_of_nonempty _ _ front nonempty, tailCutoff, Option.map_some] at cutoff
    exact (rankWordEmbedding_ordinalAction embedding front epsilon).trans (Option.some.inj cutoff)
  have bundled : rankCutoffAgreement (rankOrdinalAction (rankWordEmbedding embedding front) epsilon).val
      (embedding source) ((rankWordEmbedding embedding front).comp (rankWordEmbedding embedding tail)) := by
    rw [oldDelta, ← rankWordEmbedding_append]
    intro x z hx hz
    simpa only [rankWordEmbedding_apply] using certificate x z hx hz
  have transferred := rankApply_low_tail_certificate hl (h.critical a.length last minimum lastAt minimumAt)
    (embedding source) (rankWordEmbedding embedding front) (rankWordEmbedding embedding tail) tailBound bundled
  constructor
  · rw [naturalCutoff_append_of_nonempty _ _ _ nonempty, newTailCutoff, Option.map_some,
      ← rankWordEmbedding_ordinalAction, frontEmbedding]
  · rw [shortCopyEmbeddingValues_high hl embedding hpn hps]
    intro x z hx hz
    have wordEq :
        rankWordEmbedding (shortCopyEmbeddingValues hl embedding a.length p)
          (front.map (fun v => v + (a.length - p)) ++ tail) =
        (rankApply hl (embedding a.length) (rankWordEmbedding embedding front)).comp (rankWordEmbedding embedding tail) := by
      rw [rankWordEmbedding_append, frontEmbedding, tailEmbedding]
    rw [← rankWordEmbedding_apply, wordEq]
    exact transferred x z hx hz

end FullMarkedBLP
