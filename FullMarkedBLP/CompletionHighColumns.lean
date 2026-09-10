import FullMarkedBLP.FrozenHistoricalTrace
import FullMarkedBLP.ScanCurrentRecordGap

namespace FullMarkedBLP

/-- An event inserts no new core columns at or above a later original core
column. This excludes new columns, not only preserves old column positions. -/
theorem completionEvent_high_core_iff {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y z x : Nat}
    (event : CompletionEventGeometry a rec r y theta embedding)
    {row out : Row} (hr : rowAt a r = some row)
    (hz : z ∈ row.core) (hyz : y < z) (hzx : z ≤ x)
    (hout : rowAt (completeMark a rec r y) r = some out) :
    x ∈ out.core ↔ x ∈ row.core := by
  cases hc : completionRecord a rec r y with
  | none =>
    simp only [completeMark, hr, hc] at hout
    cases Option.some.inj hout
    rfl
  | some sources =>
    obtain ⟨k, p, nextTarget, hp, hk, hy, hnext, hs, bounds, gap, beforeOwner, packet⟩ :=
      event.2 row sources hr hc
    obtain ⟨left, right, _, _, _, _, targetGap, below, hpy⟩ :=
      rankRealization_completion_geometry event.1 hr hp hk hy hnext bounds gap beforeOwner packet
    have high : y + sources.length < z := by
      by_contra hn
      exact targetGap z hyz (by omega) hz
    simp only [completeMark, hr, hc] at hout
    rw [rowAt_set_self hr] at hout
    cases Option.some.inj hout
    rw [completeMarkRow_core_mem]
    constructor
    · intro mem
      rcases mem with old | source | target
      · exact old
      · have low := below x source
        omega
      · have bound := target
        omega
    · exact Or.inl

/-- Earlier frozen events leave the entire high-column region unchanged. -/
theorem frozen_fold_high_core_iff {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r z x : Nat} (processed : List Nat)
    (earlier : ∀ y ∈ processed, y < z)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current y => completeMark current rec r y) a) rec r mark theta embedding)
    {row out : Row} (hr : rowAt a r = some row) (hz : z ∈ row.core) (hzx : z ≤ x)
    (hout : rowAt (processed.foldl (fun current y => completeMark current rec r y) a) r = some out) :
    x ∈ out.core ↔ x ∈ row.core := by
  induction processed generalizing a row with
  | nil =>
    simp only [List.foldl_nil] at hout
    have eq := Option.some.inj (hout.symm.trans hr)
    subst out
    rfl
  | cons mark rest ih =>
    have first := events [] mark rest rfl
    have low := earlier mark (by simp)
    obtain ⟨currentRow, currentAt⟩ : ∃ rw, rowAt (completeMark a rec r mark) r = some rw := by
      cases hc : completionRecord a rec r mark with
      | none => exact ⟨row, by simp only [completeMark, hr, hc]⟩
      | some sources =>
        exact ⟨completeMarkRow row mark sources, by
          simp only [completeMark, hr, hc, rowAt_set_self hr]⟩
    have currentZ : z ∈ currentRow.core :=
      (completionEvent_high_core_iff first hr hz low (le_refl z) currentAt).mpr hz
    have tailEvents : ∀ done y suffix, rest = done ++ y :: suffix →
        CompletionEventGeometry
          (done.foldl (fun current y => completeMark current rec r y) (completeMark a rec r mark))
          rec r y theta embedding := by
      intro done y suffix he
      have next := events (mark :: done) y suffix (by simp only [List.cons_append, he])
      simpa only [List.foldl_cons] using next
    have later := ih (fun y hy => earlier y (List.mem_cons_of_mem mark hy)) tailEvents
      currentAt currentZ (by simpa only [List.foldl_cons] using hout)
    exact later.trans (completionEvent_high_core_iff first hr hz low hzx currentAt)

/-- Record target gaps survive the earlier frozen completion prefix. -/
theorem scanRankReach_frozen_record_gap {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r y target : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (processed : List Nat) (earlier : ∀ z ∈ processed, z < y)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current z => completeMark current rec r z) a) rec r mark theta embedding)
    {row out : Row} {sources : List Nat} (hr : rowAt a r = some row) (hy : y ∈ row.core)
    (hout : rowAt (processed.foldl (fun current z => completeMark current rec r z) a) r = some out)
    (record : (y, sources) ∈ rec) (ht : target ∈ out.full r) (hlt : y < target) :
    y + sources.length < target := by
  apply scanRankReach_current_record_gap reach hr record _ hlt
  change target ∈ row.core ++ [r + 1]
  change target ∈ out.core ++ [r + 1] at ht
  rcases List.mem_append.mp ht with core | endpoint
  · exact List.mem_append.mpr (Or.inl
      ((frozen_fold_high_core_iff processed earlier events hr hy hlt.le hout).mp core))
  · exact List.mem_append.mpr (Or.inr endpoint)

end FullMarkedBLP



