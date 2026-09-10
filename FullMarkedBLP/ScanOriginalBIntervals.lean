import FullMarkedBLP.FrozenHeadWidth
import FullMarkedBLP.ScanBTransport
import FullMarkedBLP.ScanStepBExact

namespace FullMarkedBLP

/-- Realizations and all frozen events strictly before a scan cursor. -/
def ScanPriorVerifiedEvents {lambda : Ordinal.{u}} (initial : Pattern)
    (initialTheta : Nat → OrdinalDomain lambda)
    (initialEmbedding : Nat → RankElementaryEmbedding lambda) (r : Nat) : Prop :=
  ∀ before history owner theta embedding,
    ScanRankReach initial initialTheta initialEmbedding before history owner theta embedding → owner < r →
    RankRowRealization before theta embedding ∧
    ∀ row, rowAt before owner = some row → ∀ done mark suffix, row.marks = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current y => completeMark current history owner y) before)
        history owner mark theta embedding

/-- One map retains every original B inside the corresponding successor interval.
Unlike exact e transport, this also covers original rows with nonempty records. -/
theorem scanRankReach_original_b_intervals {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryReal : RankRowRealization initial initialTheta initialEmbedding) :
    ∃ (phi : Nat → Nat) (original : Nat), StrictMono phi ∧ phi 0 = 0 ∧
      initial.length + r = a.length + original ∧
      (∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i) ∧
      (∀ k, phi (original + k) = r + k) ∧
      (∀ owner row, original ≤ owner → rowAt initial owner = some row →
        rowAt a (phi owner) = some ⟨row.core.map phi, row.step, row.marks.map phi⟩) ∧
      (∀ terminal ss, (terminal, ss) ∈ rec →
        ∃ i, i < original ∧ phi i = terminal ∧ phi (i + 1) = terminal + ss.length + 1) ∧
      (ScanPriorGeometry initial initialTheta initialEmbedding r →
        ScanPriorEndpointTransport initial initialTheta initialEmbedding r →
        ScanPriorVerifiedEvents initial initialTheta initialEmbedding r →
        ∀ x row v, rowAt initial x = some row → row.b = some v →
          ∃ w, (rowAt a (phi x)).bind Row.b = some w ∧ phi v ≤ w ∧ w < phi (v + 1)) := by
  induction h with
  | start =>
    refine ⟨id, 1, fun _ _ hij => hij, rfl, by omega, fun _ => ⟨rfl, rfl⟩,
      fun _ => rfl, ?_, ?_, ?_⟩
    · intro owner row _ hr
      simpa using hr
    · intro terminal ss hm; simp at hm
    · intro _ _ _ x row v hr hv
      exact ⟨v, by simp only [id_eq, hr, Option.bind_some, hv], Nat.le_refl _, Nat.lt_succ_self _⟩
  | @next before after history cursor sources oldTheta oldEmbedding reach hb hn ih =>
    obtain ⟨phi, original, mono, zero, length, holds, tail, rows, records, intervals⟩ := ih
    have newLength := native_length hn
    rw [completeFrozenMarks_length] at newLength
    have atCursor : phi original = cursor := by simpa using tail 0
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
      have keep : (terminal, ss) ∈ history →
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
        exact keep hm
      · simp only [List.isEmpty_iff, empty, if_false] at hm
        rcases List.mem_cons.mp hm with eq | old
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
          refine ⟨original, by omega, ?_, ?_⟩
          · simp [atCursor, shiftAfter]
          · dsimp only
            rw [tail 1]
            simp [shiftAfter, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        · exact keep old
    · intro geometry transport verified x row v hr hv
      have earlierGeometry := scanPriorGeometry_mono geometry (by omega : cursor ≤ cursor + sources.length + 1)
      have earlierTransport := scanPriorEndpointTransport_mono transport (by omega : cursor ≤ cursor + sources.length + 1)
      have earlierVerified : ScanPriorVerifiedEvents initial initialTheta initialEmbedding cursor := by
        intro a rec r theta embedding reached lt
        exact verified a rec r theta embedding reached (by omega)
      obtain ⟨currentReal, events⟩ := verified before history cursor oldTheta oldEmbedding reach (by omega)
      obtain ⟨completed, completedAt, _⟩ := Option.bind_eq_some_iff.mp hn
      have cb := rowAt_bounds completedAt
      obtain ⟨ownerRow, ownerAt⟩ := rowAt_exists (a := before) cb.1 (by simpa only [completeFrozenMarks_length] using cb.2)
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
        let increment := if phi v ∈ ownerRow.marks then
          ((completionRecord before history cursor (phi v)).getD []).length else 0
        have midB : completed.b = some (phi v + increment) :=
          completeFrozenMarks_b_update currentReal ownerAt currentB (events ownerRow ownerAt) completedAt
        have actual := native_b_shift (completeFrozenMarks_event_geometry ownerAt currentReal.valid (events ownerRow ownerAt)).1
          hn completedAt midB
        have upper : phi v + increment < phi (v + 1) := by
          by_cases marked : phi v ∈ ownerRow.marks
          · cases success : completionRecord before history cursor (phi v) with
            | none => simpa only [increment, marked, if_true, success, Option.getD_none,
                List.length_nil, Nat.add_zero] using mono (Nat.lt_succ_self v)
            | some packet =>
              obtain ⟨processed, splitMarks⟩ := properMarks_b_last (currentReal.valid cursor ownerRow ownerAt)
                (currentReal.proper cursor ownerRow ownerAt) currentB marked
              have prior : ∀ done mark suffix, processed = done ++ mark :: suffix →
                  CompletionEventGeometry
                    (done.foldl (fun current z => completeMark current history cursor z) before)
                    history cursor mark oldTheta oldEmbedding := by
                intro done mark suffix split
                apply events ownerRow ownerAt done mark (suffix ++ [phi v])
                simpa only [split, List.append_assoc, List.cons_append] using splitMarks
              have recordEq := realized_frozen_completionRecord_eq currentReal processed prior ownerAt marked
              obtain ⟨ss, head, width⟩ := scanRankReach_frozen_verified_head_width reach entryReal currentReal
                earlierGeometry earlierTransport processed prior ownerAt marked (recordEq.trans success)
                (events ownerRow ownerAt processed (phi v) [] splitMarks)
              obtain ⟨i, _, base, next⟩ := records (phi v) ss head
              have eq : i = v := mono.injective base
              subst i
              rw [next]
              simp only [increment, marked, if_true, success, Option.getD_some]
              omega
          · simpa only [increment, marked, if_false, Nat.add_zero] using mono (Nat.lt_succ_self v)
        refine ⟨shiftAfter cursor sources.length (phi v + increment), ?_,
          shiftAfter_le _ _ (by omega), shiftAfter_strict _ _ upper⟩
        simpa only [atCursor] using actual
      · obtain ⟨w, oldB, lower, upper⟩ := intervals earlierGeometry earlierTransport earlierVerified x row v hr hv
        obtain ⟨oldRow, atRow, atB⟩ := Option.bind_eq_some_iff.mp oldB
        have ne : phi x ≠ cursor := by
          intro same
          exact eq (mono.injective (same.trans atCursor.symm))
        have actual := scan_step_all_b_update currentReal ownerAt atRow atB (events ownerRow ownerAt) hn
        refine ⟨shiftAfter cursor sources.length w, ?_, shiftAfter_le _ _ lower, shiftAfter_strict _ _ upper⟩
        simpa only [ne, false_and, if_false, Nat.add_zero] using actual

end FullMarkedBLP
