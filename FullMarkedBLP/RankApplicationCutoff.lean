import FullMarkedBLP.RankApplicationAgreement

namespace FullMarkedBLP

theorem rankApply_evalWord_image {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (embedding : Nat → RankElementaryEmbedding lambda)
    (word : List Nat) (alpha : OrdinalDomain lambda) :
    evalWord (fun i => rankOrdinalAction (rankApply hl j (embedding i))) word (rankOrdinalAction j alpha) =
      rankOrdinalAction j (evalWord (fun i => rankOrdinalAction (embedding i)) word alpha) := by
  rw [← rankWordEmbedding_ordinalAction, ← rankApply_word, rankApply_ordinal_image, rankWordEmbedding_ordinalAction]

/-- Applying all factors and columns transports the natural cutoff exactly,
including arbitrary word lengths and the undefined empty word. -/
theorem rankApply_naturalCutoff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (embedding : Nat → RankElementaryEmbedding lambda)
    (theta : Nat → OrdinalDomain lambda) (word : List Nat) :
    naturalCutoff (fun i => rankOrdinalAction (rankApply hl j (embedding i)))
      (fun i => rankOrdinalAction j (theta i)) word =
      (naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta word).map (rankOrdinalAction j) := by
  induction word with
  | nil => rfl
  | cons v tail ih =>
    cases tail with
    | nil => rfl
    | cons w tail =>
      simp only [naturalCutoff, ih, Option.map_map]
      congr 1
      funext delta
      exact rankApply_ordinal_image hl j (embedding v) delta

/-- Natural-cutoff weak certificates for whole words transfer to application.
The actual copy branches must still identify their reindexed words and columns. -/
theorem rankApply_natural_certificate {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j owner : RankElementaryEmbedding lambda) (embedding : Nat → RankElementaryEmbedding lambda)
    (theta : Nat → OrdinalDomain lambda) (word : List Nat) {delta : OrdinalDomain lambda}
    (cutoff : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta word = some delta)
    (certificate : rankCutoffAgreement delta.val owner
      (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) word)) :
    naturalCutoff (fun i => rankOrdinalAction (rankApply hl j (embedding i)))
      (fun i => rankOrdinalAction j (theta i)) word = some (rankOrdinalAction j delta) ∧
    rankCutoffAgreement (rankOrdinalAction j delta).val (rankApply hl j owner)
      (evalWord (fun i => (rankApply hl j (embedding i) : RankDomain lambda → RankDomain lambda)) word) := by
  have bundled : rankCutoffAgreement delta.val owner (rankWordEmbedding embedding word) := by
    intro x z hx hz
    simpa only [rankWordEmbedding_apply] using certificate x z hx hz
  have transferred := rankApply_cutoffAgreement hl j bundled
  rw [rankApply_word] at transferred
  constructor
  · rw [rankApply_naturalCutoff, cutoff, Option.map_some]
  · intro x z hx hz
    simpa only [rankWordEmbedding_apply] using transferred x z hx hz

end FullMarkedBLP
