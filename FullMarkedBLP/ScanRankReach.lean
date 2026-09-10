import FullMarkedBLP.ScanEmbeddingReach

namespace FullMarkedBLP

/-- Concrete column and row-embedding evolution along the literal scan.
Completion changes rows, but does not change these semantic assignments. -/
inductive ScanRankReach {lambda : Ordinal.{u}} (initial : Pattern)
    (initialTheta : Nat → OrdinalDomain lambda)
    (initialEmbedding : Nat → RankElementaryEmbedding lambda) :
    Pattern → Records → Nat → (Nat → OrdinalDomain lambda) →
      (Nat → RankElementaryEmbedding lambda) → Prop
  | start : ScanRankReach initial initialTheta initialEmbedding initial [] 1 initialTheta initialEmbedding
  | next {a b rec r sources theta embedding} :
      ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding → r ≤ a.length →
      native (completeFrozenMarks a rec r) r = some (b, sources) →
      ScanRankReach initial initialTheta initialEmbedding b
        (if sources.isEmpty then rec else (r, sources) :: rec) (r + sources.length + 1)
        (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length)
        (nativeEmbeddingValues embedding r sources.length)

theorem scanRankReach_embeddings {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding) :
    ScanEmbeddingReach initial initialEmbedding a rec r embedding := by
  induction h with
  | start => exact ScanEmbeddingReach.start
  | next _ hb hn ih => exact ScanEmbeddingReach.next ih hb hn

theorem scanReach_rank_lift {lambda : Ordinal.{u}} {initial a : Pattern}
    {rec : Records} {r : Nat} (h : ScanReach initial a rec r)
    (initialTheta : Nat → OrdinalDomain lambda)
    (initialEmbedding : Nat → RankElementaryEmbedding lambda) :
    ∃ theta embedding, ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding := by
  induction h with
  | start => exact ⟨initialTheta, initialEmbedding, ScanRankReach.start⟩
  | next _ hb hn ih =>
    obtain ⟨theta, embedding, he⟩ := ih
    exact ⟨_, _, ScanRankReach.next he hb hn⟩

/-- Retained record targets are exactly their values at the native birth event.
No global validity premise is needed for this historical identification. -/
theorem scanRankReach_record_birth {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    {terminal : Nat} {sources : List Nat} (hm : (terminal, sources) ∈ rec) :
    ∃ before history oldTheta oldEmbedding after,
      ScanRankReach initial initialTheta initialEmbedding before history terminal oldTheta oldEmbedding ∧
      native (completeFrozenMarks before history terminal) terminal = some (after, sources) ∧
      embedding terminal = oldEmbedding terminal ∧
      (∀ i, i ≤ terminal → theta i = oldTheta i) ∧
      ∀ k, k < sources.length → theta (terminal + 1 + k) =
        nativeFreshValues oldTheta (oldEmbedding terminal) terminal sources k := by
  induction h with
  | start => simp at hm
  | @next before after history owner ss oldTheta oldEmbedding reach hb hn ih =>
    have preserve : (terminal, sources) ∈ history →
        ∃ birth birthHistory birthTheta birthEmbedding birthAfter,
          ScanRankReach initial initialTheta initialEmbedding birth birthHistory terminal birthTheta birthEmbedding ∧
          native (completeFrozenMarks birth birthHistory terminal) terminal = some (birthAfter, sources) ∧
          nativeEmbeddingValues oldEmbedding owner ss.length terminal = birthEmbedding terminal ∧
          (∀ i, i ≤ terminal →
            nativeColumnValues oldTheta (nativeFreshValues oldTheta (oldEmbedding owner) owner ss)
              owner ss.length i = birthTheta i) ∧
          ∀ k, k < sources.length →
            nativeColumnValues oldTheta (nativeFreshValues oldTheta (oldEmbedding owner) owner ss)
              owner ss.length (terminal + 1 + k) =
            nativeFreshValues birthTheta (birthEmbedding terminal) terminal sources k := by
      intro hold
      obtain ⟨birth, birthHistory, birthTheta, birthEmbedding, birthAfter, hr, hborn, he, hpre, hv⟩ := ih hold
      have hbound := scanReach_record_targets_before
        (scanEmbeddingReach_forget (scanRankReach_embeddings reach)) hold
      refine ⟨birth, birthHistory, birthTheta, birthEmbedding, birthAfter, hr, hborn, ?_, ?_, ?_⟩
      · change nativeColumnValues oldEmbedding _ owner ss.length terminal = _
        rw [nativeColumnValues_before oldEmbedding _ (by omega : terminal ≤ owner)]
        exact he
      · intro i hi
        rw [nativeColumnValues_before oldTheta _ (by omega : i ≤ owner)]
        exact hpre i hi
      · intro k hk
        rw [nativeColumnValues_before oldTheta _ (by omega : terminal + 1 + k ≤ owner)]
        exact hv k hk
    by_cases hs : ss = []
    · simp only [hs, List.isEmpty_nil, if_true] at hm
      exact preserve hm
    · simp only [List.isEmpty_iff, hs, if_false] at hm
      rcases List.mem_cons.mp hm with he | hold
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        refine ⟨before, history, oldTheta, oldEmbedding, after, reach, hn, ?_, ?_, ?_⟩
        · exact nativeColumnValues_before oldEmbedding _ (Nat.le_refl _)
        · intro i hi
          exact nativeColumnValues_before oldTheta _ hi
        · intro k hk
          exact nativeColumnValues_inserted oldTheta _ _ _ k hk
      · exact preserve hold

end FullMarkedBLP



