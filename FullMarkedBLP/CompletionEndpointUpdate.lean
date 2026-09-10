import FullMarkedBLP.CompletionAtEndpoint

namespace FullMarkedBLP

/-- Exact endpoint update for an actual completion, including an absent record. -/
theorem completionEvent_b_update {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y v : Nat}
    (event : CompletionEventGeometry a rec r y theta embedding)
    {row out : Row} (hr : rowAt a r = some row) (hb : row.b = some v)
    (hout : rowAt (completeMark a rec r y) r = some out) :
    out.b = some (v + if y = v then
      ((completionRecord a rec r y).getD []).length else 0) := by
  cases hc : completionRecord a rec r y with
  | none =>
    have same : out = row := by
      simpa only [completeMark, hr, hc, Option.some.injEq] using hout.symm
    subst out
    simpa only [hc, Option.getD_none, List.length_nil, ite_self, Nat.add_zero] using hb
  | some sources =>
    have ho := completionEvent_coreValid event r out hout
    obtain ⟨w, hw⟩ := fromRight_exists (xs := out.core) (k := 2) (by decide) ho.2.1
    by_cases he : y = v
    · subst y
      have heq : out = completeMarkRow row v sources := by
        simpa only [completeMark, hr, hc, rowAt_set_self hr, Option.some.injEq] using hout.symm
      rw [heq, completionEvent_b_at_b event hr hb hc]
      simp only [Option.getD_some, ite_true]
    · obtain ⟨k, p, nextTarget, hp, hk, hy, hnext, hs, bounds, gap, beforeOwner, packet⟩ :=
        event.2 row sources hr hc
      have le : y ≤ v := core_entry_le_b (event.1.valid r row hr) hb
        (List.mem_of_getElem? hy) (by omega)
      have eq := completionEvent_b_eq_of_mark_lt_b event hr hout ho hb hw (by omega)
      simpa only [he, ite_false, Nat.add_zero, eq] using hw

end FullMarkedBLP

