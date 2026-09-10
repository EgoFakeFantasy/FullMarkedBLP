import FullMarkedBLP.MarkTrace

namespace FullMarkedBLP

/-- Identifying a successful marked-trace computation only needs sortedness
of the owner core, rather than validity of the whole current pattern. -/
theorem computeMarkTrace_identify {a : Pattern} {r y : Nat} {row : Row} {xs ys : List Nat}
    (hr : rowAt a r = some row) (sorted : row.core.Pairwise (· < ·))
    (ht : MarkTrace a r y xs) (hc : computeMarkTrace a r y = some ys) : ys = xs := by
  obtain ⟨old, k, s, hold, hm, hk, hky, hks, trace⟩ := ht
  have he := Option.some.inj (hold.symm.trans hr)
  subst old
  have computed := computeMarkTrace_sound hr hm hc
  obtain ⟨other, j, t, hother, _, hj, hjy, hjt, trace'⟩ := computed
  have he := Option.some.inj (hother.symm.trans hr)
  subst other
  have indices := Option.some.inj ((sorted_findIdx sorted hjy).symm.trans (sorted_findIdx sorted hky))
  subst j
  have sources := Option.some.inj (hjt.symm.trans hks)
  subst t
  exact trace_unique trace' trace

/-- A known marked trace computes with the built-in budget if its length fits;
only the owner's sorted core is needed. -/
theorem computeMarkTrace_complete_of_length {a : Pattern} {r y : Nat} {row : Row} {xs : List Nat}
    (hr : rowAt a r = some row) (sorted : row.core.Pairwise (· < ·))
    (ht : MarkTrace a r y xs) (bound : xs.length ≤ y + 1) :
    computeMarkTrace a r y = some xs := by
  obtain ⟨old, k, s, hold, _, hk, hky, hks, trace⟩ := ht
  have he := Option.some.inj (hold.symm.trans hr)
  subst old
  have find := sorted_findIdx sorted hky
  have computed : computeTrace a s y = some xs := traceFuel_complete trace _ bound
  simp [computeMarkTrace, hr, find, Nat.not_lt.mpr hk, hks, computed]

end FullMarkedBLP

