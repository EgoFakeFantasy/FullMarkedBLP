import FullMarkedBLP.DirectPacket
import FullMarkedBLP.FrozenSourceBounds

namespace FullMarkedBLP

/-- Recorded direct packets survive every modification confined to the current owner. -/
theorem completion_direct_packet_in_prefix {initial a b : Pattern} {rec : Records} {r y s : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r)
    (earlier : ∀ i, i < r → rowAt b i = rowAt a i) {sources : List Nat}
    (htrace : computeMarkTrace b r y = some [y, s])
    (hc : completionRecord b rec r y = some sources) :
    sources.Nodup ∧ y + sources.length < r ∧
      ∀ x ∈ sources, Trace b x (y + ((sources.filter (· < x)).length + 1))
        [y + ((sources.filter (· < x)).length + 1), x] := by
  have hrec := recordAt_mem (((completionRecord_direct_iff htrace).mp hc).1)
  have hbound := scanReach_record_targets_before reach hrec
  have hn := (scanReach_record_decreasing historyValid reach hrec).imp (fun h => Nat.ne_of_gt h)
  refine ⟨hn, hbound, ?_⟩
  intro x hx
  have hlow := scanReach_record_sources_below historyValid reach hrec x hx
  have hrank : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  have hpred := scanReach_record_predecessor historyValid reach hrec hx
  have hpred' : predecessor b (y + ((sources.filter (· < x)).length + 1)) = some x := by
    unfold predecessor
    rw [earlier _ (by omega)]
    exact hpred
  exact Trace.next (by omega) hpred' Trace.stop

theorem frozen_completion_direct_packet {initial a : Pattern} {rec : Records} {r y s : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec r) (processed : List Nat) {sources : List Nat}
    (htrace : computeMarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y = some [y, s])
    (hc : completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y = some sources) :
    sources.Nodup ∧ y + sources.length < r ∧
      ∀ x ∈ sources, Trace (processed.foldl (fun current z => completeMark current rec r z) a)
        x (y + ((sources.filter (· < x)).length + 1))
        [y + ((sources.filter (· < x)).length + 1), x] := by
  exact completion_direct_packet_in_prefix historyValid reach
    (fun i hi => completeMarks_fold_other_row processed (by omega : i ≠ r)) htrace hc

end FullMarkedBLP

