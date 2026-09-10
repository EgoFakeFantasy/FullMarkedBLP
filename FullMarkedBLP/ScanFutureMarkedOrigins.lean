import FullMarkedBLP.ScanFutureMarkTrace
import FullMarkedBLP.ScanPriorGeometry

namespace FullMarkedBLP

/-- One coherent semantic map transports entry MarkTraces of all unscanned
owners, assuming only the geometric obligations of earlier scan events. -/
theorem scanRankReach_future_markTraces {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding) :
    ∃ (phi : Nat → Nat) (original : Nat), StrictMono phi ∧ phi 0 = 0 ∧
      initial.length + r = a.length + original ∧
      (∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i) ∧
      (∀ k, phi (original + k) = r + k) ∧
      (∀ owner row, original ≤ owner → rowAt initial owner = some row →
        rowAt a (phi owner) = some ⟨row.core.map phi, row.step, row.marks.map phi⟩) ∧
      (ScanPriorGeometry initial initialTheta initialEmbedding r →
        ∀ owner y xs, original ≤ owner → MarkTrace initial owner y xs →
          MarkTrace a (phi owner) (phi y) (xs.map phi)) ∧
      (∀ terminal sources, (terminal, sources) ∈ rec →
        ∃ i, i < original ∧ phi i = terminal ∧ phi (i + 1) = terminal + sources.length + 1) := by
  induction h with
  | start =>
    refine ⟨id, 1, fun _ _ hij => hij, rfl, by omega, fun _ => ⟨rfl, rfl⟩,
      fun _ => rfl, ?_, ?_, ?_⟩
    · intro owner row _ hr
      simpa using hr
    · intro _ owner y xs _ ht
      simpa using ht
    · intro terminal sources hm; simp at hm
  | @next before after history cursor sources oldTheta oldEmbedding reach hb hn ih =>
    obtain ⟨phi, original, hmono, hzero, hlen, holds, tail, rows, marks, records⟩ := ih
    have hnlen := native_length hn
    rw [completeFrozenMarks_length] at hnlen
    refine ⟨fun i => shiftAfter cursor sources.length (phi i), original + 1,
      fun _ _ hij => shiftAfter_strict _ _ (hmono hij), ?_, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hzero, shiftAfter]
    · intro i
      rw [nativeColumnValues_preserves, nativeEmbeddingValues_old]
      exact holds i
    · intro k
      dsimp only
      rw [Nat.add_assoc, tail (1 + k)]
      unfold shiftAfter
      rw [if_pos (by omega)]
      omega
    · intro owner row ho hr
      have hcursor : phi original = cursor := by simpa using tail 0
      have hfuture : cursor < phi owner := by rw [← hcursor]; exact hmono (by omega)
      have old := rows owner row (by omega) hr
      dsimp only
      rw [show shiftAfter cursor sources.length (phi owner) = phi owner + sources.length by
        simp [shiftAfter, hfuture]]
      rw [native_suffix_rowAt hn hfuture, completeFrozenMarks_other_row (by omega), old]
      simp only [Option.map_some, Row.shiftAfter, List.map_map, Function.comp_def]
    · intro geometry owner y xs ho ht
      obtain ⟨valid, fixed⟩ := geometry before history cursor oldTheta oldEmbedding reach (by omega)
      have old := marks (scanPriorGeometry_mono geometry (by omega)) owner y xs (by omega) ht
      have hcursor : phi original = cursor := by simpa using tail 0
      have hfuture : cursor < phi owner := by rw [← hcursor]; exact hmono (by omega)
      have transported := scan_step_future_markTrace valid fixed hn hfuture old
      simpa only [shiftAfter, if_pos hfuture, List.map_map, Function.comp_def] using transported

    · intro terminal ss hm
      have keep : (terminal, ss) ∈ history →
          ∃ i, i < original + 1 ∧ shiftAfter cursor sources.length (phi i) = terminal ∧
            shiftAfter cursor sources.length (phi (i + 1)) = terminal + ss.length + 1 := by
        intro hold
        obtain ⟨i, hib, he, hnext⟩ := records terminal ss hold
        have ht := scanReach_record_targets_before
          (scanEmbeddingReach_forget (scanRankReach_embeddings reach)) hold
        refine ⟨i, by omega, ?_, ?_⟩
        · rw [he]
          simp [shiftAfter, show ¬cursor < terminal by omega]
        · rw [hnext]
          simp [shiftAfter, show ¬cursor < terminal + ss.length + 1 by omega]
      by_cases hs : sources = []
      · simp only [hs, List.isEmpty_nil, if_true] at hm
        exact keep hm
      · simp only [List.isEmpty_iff, hs, if_false] at hm
        rcases List.mem_cons.mp hm with he | hold
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          refine ⟨original, by omega, ?_, ?_⟩
          · have ht : phi original = terminal := by simpa using tail 0
            simp [ht, shiftAfter]
          · dsimp only
            rw [tail 1]
            simp [shiftAfter, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        · exact keep hold

end FullMarkedBLP


