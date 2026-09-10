import FullMarkedBLP.NativeWalkTargetSegment

namespace FullMarkedBLP

theorem nativeSourcesFuel_above_threshold {a : Pattern} {p fuel u : Nat} {sources : List Nat}
    (h : nativeSourcesFuel a p fuel u = some sources) : ∀ x ∈ sources, p < x := by
  induction fuel generalizing u sources with
  | zero => simp [nativeSourcesFuel] at h
  | succ fuel ih =>
    obtain ⟨row, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨next, _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    next hp =>
      obtain ⟨tail, ht, he⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj he
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hp
      · exact ih ht x hx
    next =>
      have he : sources = [] := by simpa using h.symm
      simp [he]

/-- A complete lowest consecutive segment has exact source ranks, independently
of the order in which its distinct elements were emitted. -/
theorem target_segment_source_rank {sources : List Nat} {base top k : Nat}
    (hn : sources.Nodup) (above : ∀ x ∈ sources, base < x)
    (members : ∀ j, 0 < j → j ≤ top → base + j ∈ sources)
    (hk : 0 < k) (hkt : k ≤ top) :
    (sources.filter (· < base + k)).length = k - 1 := by
  let targets := (List.range (k - 1)).map (fun j => base + 1 + j)
  have htn : targets.Nodup := (after_range_sorted base (k - 1)).imp (fun hlt => Nat.ne_of_lt hlt)
  have hleft : ∀ x ∈ sources.filter (· < base + k), x ∈ targets := by
    intro x hx
    obtain ⟨hxs, hxl⟩ := List.mem_filter.mp hx
    have hlo := above x hxs
    have hhi : x < base + k := by simpa using hxl
    apply List.mem_map.mpr
    exact ⟨x - base - 1, List.mem_range.mpr (by omega), by omega⟩
  have hright : ∀ x ∈ targets, x ∈ sources.filter (· < base + k) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hjb := List.mem_range.mp hj
    apply List.mem_filter.mpr
    constructor
    · have hm := members (j + 1) (by omega) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm
    · simp; omega
  have hl := nodup_subset_length (hn.sublist List.filter_sublist) hleft
  have hr := nodup_subset_length htn hright
  have htlen : targets.length = k - 1 := by simp [targets]
  omega

theorem nativeSourcesFuel_target_segment_rank {a : Pattern} {fuel u base top k : Nat}
    {sources : List Nat} (h : nativeSourcesFuel a base fuel u = some sources)
    (entered : base + top ∈ sources)
    (chain : ∀ j, 0 < j → j ≤ top → (rowAt a (base + j)).bind Row.b = some (base + j - 1))
    (hk : 0 < k) (hkt : k ≤ top) :
    (sources.filter (· < base + k)).length = k - 1 :=
  target_segment_source_rank (nativeSourcesFuel_nodup_of_success h)
    (nativeSourcesFuel_above_threshold h)
    (nativeSourcesFuel_contains_target_segment h (Nat.le_refl _) entered chain) hk hkt

end FullMarkedBLP
