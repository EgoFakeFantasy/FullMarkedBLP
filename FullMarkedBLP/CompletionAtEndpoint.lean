import FullMarkedBLP.FrozenPredecessorGeometry
import FullMarkedBLP.CompletionEndpointBound

namespace FullMarkedBLP

/-- Completing at B extends the penultimate column by exactly the packet length. -/
theorem completeMarkRow_b_at_b {row : Row} {r y w : Nat} {sources : List Nat}
    (hv : row.CoreValid r) (hb : row.b = some y)
    (ho : (completeMarkRow row y sources).CoreValid r)
    (hw : (completeMarkRow row y sources).b = some w)
    (below : ∀ x ∈ sources, x ≤ y) (gap : y + sources.length < r) :
    w = y + sources.length := by
  have ym : y ∈ row.core := by
    unfold Row.b fromRight at hb
    split at hb
    · exact List.mem_of_getElem? hb
    · simp at hb
  have wm : w ∈ (completeMarkRow row y sources).core := by
    unfold Row.b fromRight at hw
    split at hw
    · exact List.mem_of_getElem? hw
    · simp at hw
  have wl : w < r := fromRight_lt_last ho.1 ho.2.2.1 (by decide : 1 < 2) hw
  have topMem : y + sources.length ∈ (completeMarkRow row y sources).core := by
    rw [completeMarkRow_core_mem]
    by_cases hz : sources.length = 0
    · exact Or.inl (by simpa [hz] using ym)
    · exact Or.inr (Or.inr ⟨by omega, le_refl _⟩)
  have lower := core_entry_le_b ho hw topMem gap
  have upper : w ≤ y + sources.length := by
    rcases (completeMarkRow_core_mem row y sources w).mp wm with old | source | target
    · have := core_entry_le_b hv hb old wl
      omega
    · have := below w source
      omega
    · exact target.2
  omega

/-- At an actual successful event, the endpoint increment needs no extra source bound. -/
theorem completionEvent_b_at_b {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y : Nat} {sources : List Nat}
    (event : CompletionEventGeometry a rec r y theta embedding)
    {row : Row} (hr : rowAt a r = some row) (hb : row.b = some y)
    (hc : completionRecord a rec r y = some sources) :
    (completeMarkRow row y sources).b = some (y + sources.length) := by
  have atOut : rowAt (completeMark a rec r y) r = some (completeMarkRow row y sources) := by
    rw [completeMark, hr, hc]
    exact rowAt_set_self hr
  have ho := completionEvent_coreValid event r _ atOut
  obtain ⟨w, hw⟩ := fromRight_exists (xs := (completeMarkRow row y sources).core)
    (k := 2) (by decide) ho.2.1
  obtain ⟨k, p, nextTarget, hp, hk, hy, hnext, hs, bounds, gap, beforeOwner, packet⟩ :=
    event.2 row sources hr hc
  obtain ⟨left, right, _, _, _, _, targetGap, below, hpy⟩ :=
    rankRealization_completion_geometry event.1 hr hp hk hy hnext bounds gap beforeOwner packet
  have eq := completeMarkRow_b_at_b (event.1.valid r row hr) hb ho hw
    (fun x hx => (below x hx).le.trans hpy) beforeOwner
  simpa only [eq] using hw
end FullMarkedBLP


