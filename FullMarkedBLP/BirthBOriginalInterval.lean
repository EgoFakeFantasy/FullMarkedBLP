import FullMarkedBLP.FrozenHeadWidth
import FullMarkedBLP.ScanStepBExact

namespace FullMarkedBLP

/-- At an actual scan birth, bottom B stays inside the original B's successor
interval. Earlier verified packet widths control the possible endpoint increment. -/
theorem scanRankReach_birth_b_original_interval {lambda : Ordinal.{u}} {initial a b : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    {sources : List Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (entryReal : RankRowRealization initial initialTheta initialEmbedding)
    (currentReal : RankRowRealization a theta embedding)
    (geometry : ScanPriorGeometry initial initialTheta initialEmbedding r)
    (transport : ScanPriorEndpointTransport initial initialTheta initialEmbedding r)
    {row bottom : Row} (hr : rowAt a r = some row)
    (events : ∀ done mark suffix, row.marks = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    (birth : native (completeFrozenMarks a rec r) r = some (b, sources))
    (atBottom : rowAt b r = some bottom) :
    ∃ (phi : Nat → Nat) (original : Nat) (entry : Row) (v w : Nat),
      StrictMono phi ∧ phi 0 = 0 ∧ phi original = r ∧ rowAt initial original = some entry ∧
      entry.b = some v ∧
      (∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i) ∧
      bottom.b = some w ∧ phi v ≤ w ∧ w < phi (v + 1) := by
  obtain ⟨phi, original, entry, mono, zero, owner, atEntry, shape, holds, records, _, _⟩ :=
    scanRankReach_current_mark_origins reach hr
  obtain ⟨v, atB⟩ := Row.b_exists (entryReal.valid original entry atEntry)
  have currentB : row.b = some (phi v) := by
    rw [shape]
    change fromRight (entry.core.map phi) 2 = some (phi v)
    rw [fromRight_map]
    change entry.b.map phi = some (phi v)
    simp only [atB, Option.map_some]
  let increment := if phi v ∈ row.marks then
    ((completionRecord a rec r (phi v)).getD []).length else 0
  have actual : bottom.b = some (phi v + increment) :=
    scan_step_bottom_b_update currentReal hr currentB events birth atBottom
  refine ⟨phi, original, entry, v, phi v + increment, mono, zero, owner, atEntry, atB,
    holds, actual, by omega, ?_⟩
  by_cases marked : phi v ∈ row.marks
  · cases success : completionRecord a rec r (phi v) with
    | none => simpa only [increment, marked, if_true, success, Option.getD_none, List.length_nil,
        Nat.add_zero] using mono (Nat.lt_succ_self v)
    | some packet =>
      obtain ⟨processed, splitMarks⟩ := properMarks_b_last (currentReal.valid r row hr)
        (currentReal.proper r row hr) currentB marked
      have prior : ∀ done mark suffix, processed = done ++ mark :: suffix →
          CompletionEventGeometry
            (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding := by
        intro done mark suffix eq
        apply events done mark (suffix ++ [phi v])
        simpa only [eq, List.append_assoc, List.cons_append] using splitMarks
      have recordEq := realized_frozen_completionRecord_eq currentReal processed prior hr marked
      have middleSuccess := recordEq.trans success
      obtain ⟨ss, head, width⟩ := scanRankReach_frozen_verified_head_width reach entryReal currentReal
        geometry transport processed prior hr marked middleSuccess (events processed (phi v) [] splitMarks)
      obtain ⟨i, _, base, top⟩ := records (phi v) ss head
      have eq : i = v := mono.injective base
      subst i
      rw [top]
      simp only [increment, marked, if_true, success, Option.getD_some]
      omega
  · simpa only [increment, marked, if_false, Nat.add_zero] using mono (Nat.lt_succ_self v)

end FullMarkedBLP

