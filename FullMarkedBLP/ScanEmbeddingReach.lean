import FullMarkedBLP.RecordedEmbeddingScanStep

namespace FullMarkedBLP

/-- The literal scan with the concrete native update of its row embeddings. -/
inductive ScanEmbeddingReach {lambda : Ordinal.{u}} (initial : Pattern)
    (initialEmbedding : Nat → RankElementaryEmbedding lambda) :
    Pattern → Records → Nat → (Nat → RankElementaryEmbedding lambda) → Prop
  | start : ScanEmbeddingReach initial initialEmbedding initial [] 1 initialEmbedding
  | next {a b rec r sources embedding} :
      ScanEmbeddingReach initial initialEmbedding a rec r embedding → r ≤ a.length →
      native (completeFrozenMarks a rec r) r = some (b, sources) →
      ScanEmbeddingReach initial initialEmbedding b
        (if sources.isEmpty then rec else (r, sources) :: rec)
        (r + sources.length + 1) (nativeEmbeddingValues embedding r sources.length)

theorem scanEmbeddingReach_forget {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanEmbeddingReach initial initialEmbedding a rec r embedding) :
    ScanReach initial a rec r := by
  induction h with
  | start => exact ScanReach.start
  | next _ hb hn ih => exact ScanReach.next ih hb hn

theorem scanReach_embedding_lift {lambda : Ordinal.{u}} {initial a : Pattern}
    {rec : Records} {r : Nat} (h : ScanReach initial a rec r)
    (initialEmbedding : Nat → RankElementaryEmbedding lambda) :
    ∃ embedding, ScanEmbeddingReach initial initialEmbedding a rec r embedding := by
  induction h with
  | start => exact ⟨initialEmbedding, ScanEmbeddingReach.start⟩
  | next _ hb hn ih =>
    obtain ⟨embedding, he⟩ := ih
    exact ⟨_, ScanEmbeddingReach.next he hb hn⟩

theorem scanEmbeddingReach_records_agree {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanEmbeddingReach initial initialEmbedding a rec r embedding) :
    RecordedEmbeddingsAgree embedding rec := by
  induction h with
  | start => exact recordedEmbeddingsAgree_nil _
  | next reach _ _ ih =>
    exact recordedEmbeddingsAgree_scan_step (scanEmbeddingReach_forget reach) _ ih _

end FullMarkedBLP
