import FullMarkedBLP.ScanEntryPacketCoverage
import FullMarkedBLP.ScanBirthPacketEdges

namespace FullMarkedBLP

/-- Entry natural certificates read the actual retained record packet through
mapped entry factors. Computed-trace identification and final completion-column
identification are deliberately not assumed by this semantic transfer. -/
theorem scanRankReach_entry_packet_transfer {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (increasing : ∀ i j, i < j → j ≤ a.length + 1 → theta i < theta j) :
    ∃ phi : Nat → Nat, StrictMono phi ∧ phi 0 = 0 ∧
      (∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i) ∧
      ∀ terminal sources, (terminal, sources) ∈ rec →
        ∃ i, 1 ≤ i ∧ i ≤ initial.length ∧ phi i = terminal ∧
          ∀ front owner (delta : OrdinalDomain lambda),
            naturalCutoff (fun v => rankOrdinalAction (initialEmbedding v)) initialTheta
              (front ++ [i]) = some delta →
            rankCutoffAgreement delta.val (rankWordEmbedding initialEmbedding (front ++ [i]))
              (initialEmbedding owner) →
            (∀ x ∈ sources, x ≤ terminal) →
            ∀ x ∈ sources, rankOrdinalAction (embedding (phi owner)) (theta x) =
              evalWord (fun v => rankOrdinalAction (embedding v)) (front.map phi)
                (theta (terminal + 1 + (sources.filter (· < x)).length)) := by
  obtain ⟨phi, hmono, hzero, holds, packets⟩ := scanRankReach_entry_packet_coverage h increasing
  refine ⟨phi, hmono, hzero, holds, ?_⟩
  intro terminal sources hm
  obtain ⟨i, hi, hib, he, _, covered⟩ := packets terminal sources hm
  refine ⟨i, hi, hib, he, ?_⟩
  intro front owner delta hd hc bounds x hx
  have hword : ∀ z : RankDomain lambda,
      rankWordEmbedding embedding (front.map phi ++ [terminal]) z =
        rankWordEmbedding initialEmbedding (front ++ [i]) z := by
    intro z
    rw [rankWordEmbedding_apply, rankWordEmbedding_apply]
    have hw := evalWord_reindex
      (fun v => (initialEmbedding v : RankDomain lambda → RankDomain lambda))
      (fun v => (embedding v : RankDomain lambda → RankDomain lambda)) phi (front ++ [i])
      (fun v _ => by dsimp only; rw [(holds v).2]) z
    simpa only [List.map_append, List.map_cons, List.map_nil, he] using hw
  have hcurrent : rankCutoffAgreement delta.val
      (rankWordEmbedding embedding (front.map phi ++ [terminal])) (embedding (phi owner)) := by
    rw [(holds owner).2]
    intro u z hu hz
    rw [hword z]
    exact hc u z hu hz
  have hk : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  exact rankAgreement_reads_visible_target hcurrent delta.property.le
    (covered front delta hd _ hk)
    (scanRankReach_record_word_edges h hm bounds (front.map phi) x hx)

end FullMarkedBLP
