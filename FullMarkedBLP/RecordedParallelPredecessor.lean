import FullMarkedBLP.OrderedRecordBirth
import FullMarkedBLP.NativeTargetParallelEdge
import FullMarkedBLP.NativeTraceActual

namespace FullMarkedBLP

/-- An entered lower-record segment gives retained parallel predecessors.
Birth timing, threshold equality, B-chain and output transport are derived. -/
theorem scanReach_recorded_parallel_predecessor {initial a : Pattern} {rec : Records} {r upper lower top k : Nat}
    {upperSources lowerSources : List Nat} (reach : ScanReach initial a rec r)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (upperMem : (upper, upperSources) ∈ rec) (lowerMem : (lower, lowerSources) ∈ rec)
    (lt : lower < upper) (hp : predecessor a upper = some lower)
    (entered : lower + top ∈ upperSources) (htop : top ≤ lowerSources.length)
    (hk : 0 < k) (hkt : k ≤ top) : predecessor a (upper + k) = some (lower + k) := by
  obtain ⟨before, after, history, prior, member, birth, unchanged, fullChain⟩ :=
    scanReach_ordered_birth_target_chain reach entrances upperMem lowerMem lt
  have upperBound := scanReach_record_targets_before reach upperMem
  have valid := entrances before history upper prior (by omega)
  obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp birth
  have hv := valid upper row hr
  have room := Row.step_lt_length hv.2.2.2
  obtain ⟨p, hpp⟩ := fromRight_exists (xs := row.core) (k := row.step + 1) (by omega) (by omega)
  have oldP : predecessor (completeFrozenMarks before history upper) upper = some p := by
    simp only [predecessor, hr, Option.bind_some]
    exact hpp
  have afterP := native_owner_predecessor valid birth oldP
  have currentP : predecessor a upper = some p := by
    simpa only [predecessor, unchanged upper (by omega)] using afterP
  have eq := Option.some.inj (currentP.symm.trans hp)
  subst p
  have chain := fun j hj (hjt : j ≤ top) => fullChain j hj (by omega)
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) hv.2.2.2.1 (by omega)
  have source := native_sources_of_success birth
  have nonempty : upperSources ≠ [] := by intro eq; simp [eq] at entered
  have walk := nativeSources_nonempty_fuel hr hpp he source nonempty
  have sourceMember := nativeSourcesFuel_contains_target_segment walk (Nat.le_refl _) entered chain k hk hkt
  have rank := nativeSourcesFuel_target_segment_rank walk entered chain hk hkt
  have rankBound : (upperSources.filter (· < lower + k)).length < upperSources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨lower + k, sourceMember, by simp⟩
  have indexBound : k ≤ upperSources.length := by omega
  have edge := native_target_segment_predecessor valid birth oldP entered chain hk hkt
  simpa only [predecessor, unchanged (upper + k) (by omega)] using edge

end FullMarkedBLP
