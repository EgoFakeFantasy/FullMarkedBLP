import FullMarkedBLP.CopySemanticValues
import FullMarkedBLP.NaturalCutoffReindexExact
import FullMarkedBLP.RankApplicationCutoff

namespace FullMarkedBLP

theorem shortCopy_prefix_natural_certificate {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {a : Pattern} {theta : Nat → OrdinalDomain lambda}
    {embedding : Nat → RankElementaryEmbedding lambda} (h : RankRowRealization a theta embedding)
    {last : Row} {p r : Nat} (lastAt : rowAt a a.length = some last) (hp : last.p = some p)
    (before : r < a.length) (word : List Nat) (bounded : ∀ v ∈ word, v < a.length)
    {delta : OrdinalDomain lambda}
    (cutoff : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta word = some delta)
    (certificate : rankCutoffAgreement delta.val (embedding r)
      (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) word)) :
    naturalCutoff (fun i => rankOrdinalAction (shortCopyEmbeddingValues hl embedding a.length p i))
      (shortCopyColumnValues theta (embedding a.length) a.length p) word = some delta ∧
    rankCutoffAgreement delta.val (shortCopyEmbeddingValues hl embedding a.length p r)
      (evalWord (fun i => (shortCopyEmbeddingValues hl embedding a.length p i :
        RankDomain lambda → RankDomain lambda)) word) := by
  have factors : ∀ v ∈ word, shortCopyEmbeddingValues hl embedding a.length p (id v) = embedding v := by
    intro v hv
    exact if_pos (bounded v hv)
  have successors : ∀ v ∈ word,
      shortCopyColumnValues theta (embedding a.length) a.length p (id v + 1) = theta (v + 1) := by
    intro v hv
    change shortCopyColumnValues theta (embedding a.length) a.length p (v + 1) = theta (v + 1)
    exact shortCopyColumnValues_prefix h lastAt hp (by have := bounded v hv; omega)
  have same := naturalCutoff_reindex_eq
    (fun i => rankOrdinalAction (embedding i))
    (fun i => rankOrdinalAction (shortCopyEmbeddingValues hl embedding a.length p i))
    theta (shortCopyColumnValues theta (embedding a.length) a.length p) id word
    (fun v hv => congrArg rankOrdinalAction (factors v hv)) successors
  constructor
  · simpa only [List.map_id] using same.trans cutoff
  · rw [shortCopyEmbeddingValues, if_pos before]
    intro x z hx hz
    have words := evalWord_reindex
      (fun i => (embedding i : RankDomain lambda → RankDomain lambda))
      (fun i => (shortCopyEmbeddingValues hl embedding a.length p i : RankDomain lambda → RankDomain lambda))
      id word (fun v hv => by dsimp only; rw [factors v hv]) z
    simp only [List.map_id] at words
    rw [words]
    exact certificate x z hx hz

/-- The all-high factor word has exactly the image natural cutoff and
the transferred weak certificate under the concrete copied assignments. -/
theorem shortCopy_high_natural_certificate {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (theta : Nat → OrdinalDomain lambda) (embedding : Nat → RankElementaryEmbedding lambda)
    {n p source : Nat} (hpn : p ≤ n) (hps : p ≤ source)
    (word : List Nat) (high : ∀ v ∈ word, p ≤ v) {delta : OrdinalDomain lambda}
    (cutoff : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta word = some delta)
    (certificate : rankCutoffAgreement delta.val (embedding source)
      (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) word)) :
    naturalCutoff (fun i => rankOrdinalAction (shortCopyEmbeddingValues hl embedding n p i))
      (shortCopyColumnValues theta (embedding n) n p) (word.map (fun v => v + (n - p))) =
        some (rankOrdinalAction (embedding n) delta) ∧
    rankCutoffAgreement (rankOrdinalAction (embedding n) delta).val
      (shortCopyEmbeddingValues hl embedding n p (source + (n - p)))
      (evalWord (fun i => (shortCopyEmbeddingValues hl embedding n p i : RankDomain lambda → RankDomain lambda))
        (word.map (fun v => v + (n - p)))) := by
  obtain ⟨appliedCutoff, appliedCertificate⟩ :=
    rankApply_natural_certificate hl (embedding n) (embedding source) embedding theta word cutoff certificate
  have factors : ∀ v ∈ word,
      shortCopyEmbeddingValues hl embedding n p (v + (n - p)) = rankApply hl (embedding n) (embedding v) :=
    fun v hv => shortCopyEmbeddingValues_high hl embedding hpn (high v hv)
  have successors : ∀ v ∈ word,
      shortCopyColumnValues theta (embedding n) n p (v + (n - p) + 1) =
        rankOrdinalAction (embedding n) (theta (v + 1)) := by
    intro v hv
    have same : v + (n - p) + 1 = (v + 1) + (n - p) := by omega
    rw [same]
    exact shortCopyColumnValues_high theta (embedding n) hpn (by have := high v hv; omega)
  have sameCutoff := naturalCutoff_reindex_eq
    (fun i => rankOrdinalAction (rankApply hl (embedding n) (embedding i)))
    (fun i => rankOrdinalAction (shortCopyEmbeddingValues hl embedding n p i))
    (fun i => rankOrdinalAction (embedding n) (theta i)) (shortCopyColumnValues theta (embedding n) n p)
    (fun v => v + (n - p)) word (fun v hv => congrArg rankOrdinalAction (factors v hv)) successors
  refine ⟨sameCutoff.trans appliedCutoff, ?_⟩
  rw [shortCopyEmbeddingValues_high hl embedding hpn hps]
  intro x z hx hz
  have words := evalWord_reindex
    (fun i => (rankApply hl (embedding n) (embedding i) : RankDomain lambda → RankDomain lambda))
    (fun i => (shortCopyEmbeddingValues hl embedding n p i : RankDomain lambda → RankDomain lambda))
    (fun v => v + (n - p)) word (fun v hv => by dsimp only; rw [factors v hv]) z
  rw [words]
  exact appliedCertificate x z hx hz

end FullMarkedBLP
