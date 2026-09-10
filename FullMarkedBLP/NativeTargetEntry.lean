import FullMarkedBLP.NativeTargetSourceRank

namespace FullMarkedBLP

/-- Starting immediately above a consecutive target segment forces entry;
no separate membership hypothesis is needed. -/
theorem nativeSourcesFuel_target_entry {a : Pattern} {fuel base top : Nat}
    {sources : List Nat}
    (h : nativeSourcesFuel a base fuel (base + top + 1) = some sources)
    (hb : (rowAt a (base + top + 1)).bind Row.b = some (base + top))
    (ht : 0 < top) : base + top ∈ sources :=
  nativeSourcesFuel_first_mem h hb (by omega)

/-- A walk starting just above a complete consecutive B segment has exactly
that many sources, rather than merely containing the segment. -/
theorem nativeSourcesFuel_target_segment_exact_length {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {fuel base top : Nat} {sources : List Nat}
    (h : nativeSourcesFuel a base fuel (base + top + 1) = some sources)
    (chain : ∀ j, 0 < j → j ≤ top + 1 →
      (rowAt a (base + j)).bind Row.b = some (base + j - 1)) :
    sources.length = top := by
  have bounds := nativeSourcesFuel_bounds valid h
  let targets := (List.range top).map (fun j => base + 1 + j)
  have upper : sources.length ≤ top := by
    have hh := nodup_subset_length (nativeSourcesFuel_nodup_of_success h) (ys := targets) (by
      intro x hx
      have hb := bounds x hx
      apply List.mem_map.mpr
      exact ⟨x - base - 1, List.mem_range.mpr (by omega), by omega⟩)
    simpa [targets] using hh
  by_cases ht : 0 < top
  · have hb : (rowAt a (base + top + 1)).bind Row.b = some (base + top) := by
      have hh := chain (top + 1) (by omega) (Nat.le_refl _)
      simpa only [Nat.add_assoc, Nat.add_sub_cancel] using hh
    have entered := nativeSourcesFuel_target_entry h hb ht
    have lower := nativeSourcesFuel_target_segment_length h (Nat.le_refl _) entered
      (fun j hj hjt => chain j hj (by omega))
    omega
  · omega

end FullMarkedBLP
