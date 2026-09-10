import FullMarkedBLP.ScanRecords

namespace FullMarkedBLP

/-- An actual scan retains exactly one source list for each recorded owner. -/
theorem scanReach_record_unique {initial a : Pattern} {rec : Records} {r owner : Nat}
    {xs ys : List Nat} (reach : ScanReach initial a rec r)
    (left : (owner, xs) ∈ rec) (right : (owner, ys) ∈ rec) : xs = ys := by
  obtain ⟨i, hi, atI⟩ := List.mem_iff_getElem.mp left
  obtain ⟨j, hj, atJ⟩ := List.mem_iff_getElem.mp right
  have ordered := scanReach_records_ordered reach
  have equal : i = j := by
    by_cases lt : i < j
    · have h := List.pairwise_iff_getElem.mp ordered i j hi hj lt
      rw [atI, atJ] at h
      exact False.elim (Nat.lt_irrefl owner h)
    · by_cases gt : j < i
      · have h := List.pairwise_iff_getElem.mp ordered j i hj hi gt
        rw [atJ, atI] at h
        exact False.elim (Nat.lt_irrefl owner h)
      · omega
  subst j
  exact congrArg Prod.snd (atI.symm.trans atJ)

end FullMarkedBLP
