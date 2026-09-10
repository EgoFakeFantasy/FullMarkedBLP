import FullMarkedBLP.CopyVerifiedWidthEquality

namespace FullMarkedBLP

/-- One coherent map places every original B at its original column image or
at the top of that image's retained record. All packet equalities used here
belong to strictly earlier, already verified scan events. -/
theorem shortCopy_scan_b_boundaries {lambda : Ordinal.{u}} {parent copied a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (parentValid : ∀ i row, rowAt parent i = some row → row.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (h : ScanRankReach copied initialTheta initialEmbedding a rec r theta embedding)
    (entryReal : RankRowRealization copied initialTheta initialEmbedding) :
    ∃ (phi : Nat → Nat) (original : Nat), StrictMono phi ∧ phi 0 = 0 ∧
      copied.length + r = a.length + original ∧
      (∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i) ∧
      (∀ k, phi (original + k) = r + k) ∧
      (∀ owner row, original ≤ owner → rowAt copied owner = some row →
        rowAt a (phi owner) = some ⟨row.core.map phi, row.step, row.marks.map phi⟩) ∧
      (∀ terminal ss, (terminal, ss) ∈ rec →
        ∃ i, i < original ∧ phi i = terminal ∧ phi (i + 1) = terminal + ss.length + 1) ∧
      (ScanPriorVerifiedEvents copied initialTheta initialEmbedding r →
        ∀ x row v, rowAt copied x = some row → row.b = some v →
          (rowAt a (phi x)).bind Row.b = some (phi v) ∨
          ∃ ss, (phi v, ss) ∈ rec ∧ (rowAt a (phi x)).bind Row.b = some (phi v + ss.length)) := by
  induction h with
  | start =>
    refine ⟨id, 1, fun _ _ hij => hij, rfl, by omega, fun _ => ⟨rfl, rfl⟩,
      fun _ => rfl, ?_, ?_, ?_⟩
    · intro owner row _ hr; simpa using hr
    · intro terminal ss hm; simp at hm
    · intro _ x row v hr hv
      exact Or.inl (by simp only [id_eq, hr, Option.bind_some, hv])
  | @next before after history cursor sources oldTheta oldEmbedding reach hb hn ih =>
    obtain ⟨phi, original, mono, zero, lengths, holds, tail, rows, records, boundaries⟩ := ih
    have newLength := native_length hn
    rw [completeFrozenMarks_length] at newLength
    have atCursor : phi original = cursor := by simpa using tail 0
    have keep : ∀ base ss, (base, ss) ∈ history →
        (base, ss) ∈ (if sources.isEmpty then history else (cursor, sources) :: history) := by
      intro base ss member
      split <;> simp_all
    refine ⟨fun i => shiftAfter cursor sources.length (phi i), original + 1,
      fun _ _ hij => shiftAfter_strict _ _ (mono hij), ?_, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · simp [zero, shiftAfter]
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
      have future : cursor < phi owner := by rw [← atCursor]; exact mono (by omega)
      have old := rows owner row (by omega) hr
      dsimp only
      rw [show shiftAfter cursor sources.length (phi owner) = phi owner + sources.length by
        simp [shiftAfter, future]]
      rw [native_suffix_rowAt hn future, completeFrozenMarks_other_row (by omega), old]
      simp only [Option.map_some, Row.shiftAfter, List.map_map, Function.comp_def]
    · intro terminal ss hm
      have oldRecord : (terminal, ss) ∈ history →
          ∃ i, i < original + 1 ∧ shiftAfter cursor sources.length (phi i) = terminal ∧
            shiftAfter cursor sources.length (phi (i + 1)) = terminal + ss.length + 1 := by
        intro old
        obtain ⟨i, hi, base, next⟩ := records terminal ss old
        have bound := scanReach_record_targets_before
          (scanEmbeddingReach_forget (scanRankReach_embeddings reach)) old
        refine ⟨i, by omega, ?_, ?_⟩
        · rw [base]; simp [shiftAfter, show ¬cursor < terminal by omega]
        · rw [next]; simp [shiftAfter, show ¬cursor < terminal + ss.length + 1 by omega]
      by_cases empty : sources = []
      · simp only [empty, List.isEmpty_nil, if_true] at hm
        exact oldRecord hm
      · simp only [List.isEmpty_iff, empty, if_false] at hm
        rcases List.mem_cons.mp hm with eq | old
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
          refine ⟨original, by omega, ?_, ?_⟩
          · simp [atCursor, shiftAfter]
          · dsimp only
            rw [tail 1]
            simp [shiftAfter, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        · exact oldRecord old
    · intro verified x row v hr hv
      have prior : ScanPriorVerifiedEvents copied initialTheta initialEmbedding cursor := by
        intro a rec r theta embedding reached lt
        exact verified a rec r theta embedding reached (by omega)
      obtain ⟨currentReal, events⟩ := verified before history cursor oldTheta oldEmbedding reach (by omega)
      obtain ⟨completed, completedAt, _⟩ := Option.bind_eq_some_iff.mp hn
      have cb := rowAt_bounds completedAt
      obtain ⟨ownerRow, ownerAt⟩ := rowAt_exists (a := before) cb.1 (by simpa only [completeFrozenMarks_length] using cb.2)
      have plain := scanEmbeddingReach_forget (scanRankReach_embeddings reach)
      have frozenValid := (completeFrozenMarks_event_geometry ownerAt currentReal.valid (events ownerRow ownerAt)).1
      by_cases eq : x = original
      · subst x
        have mappedAt := rows original row (Nat.le_refl _) hr
        rw [atCursor, ownerAt] at mappedAt
        have shape := Option.some.inj mappedAt
        have currentB : ownerRow.b = some (phi v) := by
          rw [shape]
          change fromRight (row.core.map phi) 2 = some (phi v)
          rw [fromRight_map]
          change row.b.map phi = some (phi v)
          simp only [hv, Option.map_some]
        have completedB := completeFrozenMarks_b_update currentReal ownerAt currentB (events ownerRow ownerAt) completedAt
        by_cases marked : phi v ∈ ownerRow.marks
        · cases success : completionRecord before history cursor (phi v) with
          | none =>
            have unchanged : completed.b = some (phi v) := by
              simpa only [marked, if_true, success, Option.getD_none, List.length_nil, Nat.add_zero] using completedB
            exact Or.inl (by simpa only [atCursor] using native_b_shift frozenValid hn completedAt unchanged)
          | some packet =>
            obtain ⟨processed, splitMarks⟩ := properMarks_b_last (currentReal.valid cursor ownerRow ownerAt)
              (currentReal.proper cursor ownerRow ownerAt) currentB marked
            have priorEvents : ∀ done mark suffix, processed = done ++ mark :: suffix →
                CompletionEventGeometry
                  (done.foldl (fun current z => completeMark current history cursor z) before)
                  history cursor mark oldTheta oldEmbedding := by
              intro done mark suffix split
              apply events ownerRow ownerAt done mark (suffix ++ [phi v])
              simpa only [split, List.append_assoc, List.cons_append] using splitMarks
            have recordEq := realized_frozen_completionRecord_eq currentReal processed priorEvents ownerAt marked
            obtain ⟨ss, head, width⟩ := shortCopy_verified_completion_width_eq parentValid sat copy reach entryReal
              currentReal prior processed priorEvents ownerAt marked (recordEq.trans success)
              (events ownerRow ownerAt processed (phi v) [] splitMarks)
            have actualB : completed.b = some (phi v + ss.length) := by
              simpa only [marked, if_true, success, Option.getD_some, width] using completedB
            have topBefore := scanReach_record_targets_before plain head
            have fixedBase : shiftAfter cursor sources.length (phi v) = phi v := by
              simp [shiftAfter, show ¬cursor < phi v by omega]
            have fixedTop : shiftAfter cursor sources.length (phi v + ss.length) = phi v + ss.length := by
              simp [shiftAfter, show ¬cursor < phi v + ss.length by omega]
            refine Or.inr ⟨ss, ?_, ?_⟩
            · simpa only [fixedBase] using keep _ _ head
            · simpa only [atCursor, fixedBase, fixedTop] using native_b_shift frozenValid hn completedAt actualB
        · have unchanged : completed.b = some (phi v) := by
            simpa only [marked, if_false, Nat.add_zero] using completedB
          exact Or.inl (by simpa only [atCursor] using native_b_shift frozenValid hn completedAt unchanged)
      · have ne : phi x ≠ cursor := by
          intro same
          exact eq (mono.injective (same.trans atCursor.symm))
        have moved : ∀ w, (rowAt before (phi x)).bind Row.b = some w →
            (rowAt after (shiftAfter cursor sources.length (phi x))).bind Row.b = some (shiftAfter cursor sources.length w) := by
          intro w oldB
          obtain ⟨oldRow, atRow, atB⟩ := Option.bind_eq_some_iff.mp oldB
          have actual := scan_step_all_b_update currentReal ownerAt atRow atB (events ownerRow ownerAt) hn
          simpa only [ne, false_and, if_false, Nat.add_zero] using actual
        rcases boundaries prior x row v hr hv with unchanged | ⟨ss, member, atB⟩
        · exact Or.inl (moved _ unchanged)
        · have topBefore := scanReach_record_targets_before plain member
          have fixedBase : shiftAfter cursor sources.length (phi v) = phi v := by
            simp [shiftAfter, show ¬cursor < phi v by omega]
          have fixedTop : shiftAfter cursor sources.length (phi v + ss.length) = phi v + ss.length := by
            simp [shiftAfter, show ¬cursor < phi v + ss.length by omega]
          refine Or.inr ⟨ss, ?_, ?_⟩
          · simpa only [fixedBase] using keep _ _ member
          · simpa only [fixedBase, fixedTop] using moved _ atB

end FullMarkedBLP
