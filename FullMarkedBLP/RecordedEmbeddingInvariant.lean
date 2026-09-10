import FullMarkedBLP.DirectPacketRealizedEdges

namespace FullMarkedBLP

def RecordedEmbeddingsAgree {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) (rec : Records) : Prop :=
  ∀ terminal sources, (terminal, sources) ∈ rec → ∀ k, k ≤ sources.length →
    embedding (terminal + k) = embedding terminal

theorem recordedEmbeddingsAgree_nil {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) : RecordedEmbeddingsAgree embedding [] := by
  intro terminal sources hm
  simp at hm

theorem recordedEmbeddingsAgree_native_step {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) {rec : Records} {r : Nat}
    (h : RecordedEmbeddingsAgree embedding rec)
    (hb : ∀ terminal sources, (terminal, sources) ∈ rec → terminal + sources.length < r)
    (sources : List Nat) :
    RecordedEmbeddingsAgree (nativeEmbeddingValues embedding r sources.length) ((r, sources) :: rec) := by
  intro terminal ss hm k hk
  rcases List.mem_cons.mp hm with he | hm
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    rw [nativeEmbeddingValues_block embedding terminal ss.length k hk]
    exact (nativeEmbeddingValues_block embedding terminal ss.length 0 (Nat.zero_le _)).symm
  · have hbound := hb terminal ss hm
    unfold nativeEmbeddingValues
    rw [nativeColumnValues_before embedding _ (by omega : terminal + k ≤ r),
      nativeColumnValues_before embedding _ (by omega : terminal ≤ r)]
    exact h terminal ss hm k hk

end FullMarkedBLP

