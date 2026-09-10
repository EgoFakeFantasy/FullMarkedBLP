import FullMarkedBLP.ScanCurrentMarkOrigins
import FullMarkedBLP.ScanOriginalMap
import FullMarkedBLP.MarkTraceIdentification
import FullMarkedBLP.RankCutoffBounds

namespace FullMarkedBLP

/-- Every current entry mark inherits its original historical certificate and
an exact mapped marked trace. Its current natural cutoff may differ. -/
theorem scanRankReach_current_bounded_historical_certificates {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryRealization : RankRowRealization initial initialTheta initialEmbedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    {current : Row} (hr : rowAt a r = some current) :
    ∃ phi : Nat → Nat, StrictMono phi ∧
      (∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i) ∧
      (∀ terminal sources, (terminal, sources) ∈ rec →
        ∃ i, phi i = terminal ∧ phi (i + 1) = terminal + sources.length + 1) ∧
      ∀ y ∈ current.marks, ∃ (xs : List Nat) (delta : OrdinalDomain lambda),
        MarkTrace a r y (xs.map phi) ∧
        computeMarkTrace a r y = some (xs.map phi) ∧
        naturalCutoff (fun i => rankOrdinalAction (initialEmbedding i)) initialTheta xs.dropLast = some delta ∧
        (∀ ss, (y, ss) ∈ rec → delta ≤ theta (y + ss.length + 1)) ∧
        rankCutoffAgreement delta.val (embedding r)
          (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) (xs.dropLast.map phi)) := by
  obtain ⟨phi, original, entry, hmono, _, mapped, he, shape, holds, records, members, traces⟩ :=
    scanRankReach_current_mark_origins h hr
  have sorted : current.core.Pairwise (· < ·) := by
    rw [shape]
    exact List.pairwise_map.mpr ((entryRealization.valid original entry he).1.imp (fun hlt => hmono hlt))
  refine ⟨phi, hmono, holds, ?_, ?_⟩
  · intro terminal sources hm
    obtain ⟨i, _, hi, hn⟩ := records terminal sources hm
    exact ⟨i, hi, hn⟩
  intro y hy
  obtain ⟨v, hv, hvy⟩ := (members y).mp hy
  obtain ⟨k, s, xs, delta, hk, hky, hks, ht, hd, hc⟩ :=
    entryRealization.marked original entry v he hv
  have old : MarkTrace initial original v xs := ⟨entry, k, s, he, hv, hk, hky, hks, ht⟩
  have transported : MarkTrace a r y (xs.map phi) := by
    simpa only [hvy] using traces geometry v xs old
  refine ⟨xs, delta, transported, ?_, hd, ?_, ?_⟩
  · apply computeMarkTrace_complete_of_length hr sorted transported
    have length := trace_length_bound entryRealization.valid ht
    have extensive : ∀ i, i ≤ phi i := by
      intro i; induction i with
      | zero => omega
      | succ i ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hmono (Nat.lt_succ_self i)))
    have hv := extensive v
    simp only [List.length_map]
    omega
  · intro ss member
    obtain ⟨i, _, hi, successor⟩ := records y ss member
    have same : i = v := hmono.injective (hi.trans hvy.symm)
    subst i
    have bound := (rankRealization_trace_cutoff_bounds entryRealization ht hd).2
    rw [← successor, (holds (v + 1)).1]
    exact bound
  · rw [← mapped, (holds original).2]
    intro x z hx hz
    have word := evalWord_reindex
      (fun i => (initialEmbedding i : RankDomain lambda → RankDomain lambda))
      (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) phi xs.dropLast
      (fun i _ => by dsimp only; rw [(holds i).2]) z
    rw [word]
    exact hc x z hx hz

end FullMarkedBLP







