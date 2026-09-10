import FullMarkedBLP.ScanRecordedTargetB
import FullMarkedBLP.NativeWalkUnique

namespace FullMarkedBLP

theorem nativeSourcesFuel_first_mem {a : Pattern} {p fuel u v : Nat} {sources : List Nat}
    (h : nativeSourcesFuel a p fuel u = some sources)
    (hb : (rowAt a u).bind Row.b = some v) (hp : p < v) : v ∈ sources := by
  cases fuel with
  | zero => simp [nativeSourcesFuel] at h
  | succ fuel =>
    obtain ⟨row, hr, hrv⟩ := Option.bind_eq_some_iff.mp hb
    simp only [nativeSourcesFuel, hr] at h
    dsimp only [Bind.bind, Option.bind] at h
    rw [hrv] at h
    dsimp only [Bind.bind, Option.bind] at h
    rw [if_pos hp] at h
    obtain ⟨tail, _, he⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj he
    simp

/-- A successful B walk contains the next above-threshold B value of every
source it emits. No global validity assumption is required. -/
theorem nativeSourcesFuel_closed_under_b {a : Pattern} {p fuel u x v : Nat} {sources : List Nat}
    (h : nativeSourcesFuel a p fuel u = some sources) (hx : x ∈ sources)
    (hb : (rowAt a x).bind Row.b = some v) (hp : p < v) : v ∈ sources := by
  induction fuel generalizing u sources with
  | zero => simp [nativeSourcesFuel] at h
  | succ fuel ih =>
    obtain ⟨row, hr, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨next, hn, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    next =>
      obtain ⟨tail, ht, he⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj he
      rcases List.mem_cons.mp hx with he | hm
      · subst next
        exact List.mem_cons_of_mem _ (nativeSourcesFuel_first_mem ht hb hp)
      · exact List.mem_cons_of_mem _ (ih ht hm)
    next =>
      have he : sources = [] := by simpa using h.symm
      simp [he] at hx

/-- Once a B walk emits a target, it emits every positive lower target in a
consecutive B block, provided the threshold is no higher than the block base. -/
theorem nativeSourcesFuel_contains_target_segment {a : Pattern} {p fuel u base top : Nat}
    {sources : List Nat} (h : nativeSourcesFuel a p fuel u = some sources) (hp : p ≤ base)
    (entered : base + top ∈ sources)
    (chain : ∀ j, 0 < j → j ≤ top → (rowAt a (base + j)).bind Row.b = some (base + j - 1)) :
    ∀ k, 0 < k → k ≤ top → base + k ∈ sources := by
  revert entered chain
  induction top with
  | zero => intro _ _ k hk hkt; omega
  | succ top ih =>
    intro entered chain k hk hkt
    by_cases he : k = top + 1
    · simpa [he] using entered
    · have htop : 0 < top := by omega
      have hprevious : base + top ∈ sources := by
        have hb := chain (top + 1) (by omega) (Nat.le_refl _)
        have hh := nativeSourcesFuel_closed_under_b h entered hb (by omega)
        simpa using hh
      exact ih hprevious (fun j hj hji => chain j hj (by omega)) k hk (by omega)

/-- Entering a retained record's target segment forces inclusion in the new
source walk; the earlier native validity obligation is explicitly bounded. -/
theorem scan_record_targets_in_native_walk {initial a : Pattern} {rec : Records} {cursor : Nat}
    (reach : ScanReach initial a rec cursor)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < cursor →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    {terminal : Nat} {recorded : List Nat} (hm : (terminal, recorded) ∈ rec)
    {p fuel u top : Nat} {sources : List Nat}
    (h : nativeSourcesFuel a p fuel u = some sources) (hp : p ≤ terminal)
    (entered : terminal + top ∈ sources) (htop : top ≤ recorded.length) :
    ∀ k, 0 < k → k ≤ top → terminal + k ∈ sources := by
  apply nativeSourcesFuel_contains_target_segment h hp entered
  intro j hj hji
  exact scanReach_record_target_b reach entrances hm hj (by omega)

theorem nativeSourcesFuel_target_segment_length {a : Pattern} {p fuel u base top : Nat}
    {sources : List Nat} (h : nativeSourcesFuel a p fuel u = some sources) (hp : p ≤ base)
    (entered : base + top ∈ sources)
    (chain : ∀ j, 0 < j → j ≤ top → (rowAt a (base + j)).bind Row.b = some (base + j - 1)) :
    top ≤ sources.length := by
  have members := nativeSourcesFuel_contains_target_segment h hp entered chain
  have hnodup := (after_range_sorted base top).imp (fun hlt => Nat.ne_of_lt hlt)
  have hlen := nodup_subset_length hnodup (ys := sources) (by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hjb := List.mem_range.mp hj
    have hm := members (j + 1) (by omega) (by omega)
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm)
  simpa only [List.length_map, List.length_range] using hlen

end FullMarkedBLP



