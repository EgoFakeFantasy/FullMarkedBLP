import FullMarkedBLP.RecordedLastEndpoint

namespace FullMarkedBLP

/-- The current record predecessor is exactly its actual birth native threshold. -/
theorem scanReach_record_birth_threshold {initial a : Pattern} {rec : Records} {r : Nat}
    (reach : ScanReach initial a rec r)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    {terminal : Nat} {sources : List Nat} (member : (terminal, sources) ∈ rec) :
    ∃ before after history, ScanReach initial before history terminal ∧
      native (completeFrozenMarks before history terminal) terminal = some (after, sources) ∧
      predecessor (completeFrozenMarks before history terminal) terminal = predecessor a terminal ∧
      ∀ i, i ≤ terminal + sources.length → rowAt a i = rowAt after i := by
  obtain ⟨before, after, history, prior, _, birth, unchanged⟩ := scanReach_record_origin_prefix reach member
  have bound := scanReach_record_targets_before reach member
  have valid := entrances before history terminal prior (by omega)
  have source := native_sources_of_success birth
  obtain ⟨old, oldAt, _⟩ := Option.bind_eq_some_iff.mp birth
  have hv := valid terminal old oldAt
  have room := Row.step_lt_length hv.2.2.2
  obtain ⟨p, hp⟩ := fromRight_exists (xs := old.core) (k := old.step + 1) (by omega) (by omega)
  obtain ⟨e, he⟩ := fromRight_exists (xs := old.core) (k := old.step) hv.2.2.2.1 (by omega)
  have nonempty : sources ≠ [] := ((scanReach_records_before reach).2 (terminal, sources) member).2.2
  have length : 0 < sources.length := List.length_pos_iff.mpr nonempty
  obtain ⟨last, hl⟩ := fromRight_exists (xs := sources) (k := 1) (by omega) (by omega)
  have lastAt : sources.getLast? = some last := by
    simpa [fromRight, show 1 ≤ sources.length by omega, List.getLast?_eq_getElem?] using hl
  obtain ⟨bottom, _, _, bottomAt, bottomP, endpoint, _⟩ :=
    native_bottom_sat_witness valid oldAt hp he source lastAt birth
  have currentAt := (unchanged terminal (by omega)).trans bottomAt
  refine ⟨before, after, history, prior, birth, ?_, unchanged⟩
  simp only [predecessor, oldAt, currentAt, Option.bind_some, bottomP]
  exact hp

end FullMarkedBLP

