import FullMarkedBLP.FrozenHistoricalTrace

namespace FullMarkedBLP

/-- The guard reads only rows named by nonterminal factors. -/
theorem currentPlusOne_rows_eq {a b : Pattern} {xs : List Nat}
    (rows : ∀ i ∈ xs.dropLast, rowAt b i = rowAt a i) :
    currentPlusOne b xs = currentPlusOne a xs := by
  apply Bool.eq_iff_iff.mpr
  rw [currentPlusOne_iff, currentPlusOne_iff]
  constructor
  · intro guard parent child pair
    obtain ⟨row, hr, hm⟩ := guard parent child pair
    exact ⟨row, (rows parent (List.of_mem_zip pair).1).symm.trans hr, hm⟩
  · intro guard parent child pair
    obtain ⟨row, hr, hm⟩ := guard parent child pair
    exact ⟨row, (rows parent (List.of_mem_zip pair).1).trans hr, hm⟩

/-- Arbitrary current-owner completion prefixes leave the guard on earlier
factor rows unchanged, without any semantic event assumptions. -/
theorem frozen_currentPlusOne_eq {a : Pattern} {rec : Records} {r : Nat}
    (processed : List Nat) {xs : List Nat} (below : ∀ i ∈ xs.dropLast, i < r) :
    currentPlusOne (processed.foldl (fun current y => completeMark current rec r y) a) xs =
      currentPlusOne a xs := by
  apply currentPlusOne_rows_eq
  intro i hi
  exact completeMarks_fold_other_row processed (Nat.ne_of_lt (below i hi))

/-- Once the actual word is preserved, the entire record lookup is preserved;
this includes unsuccessful lookups and guard failures. -/
theorem frozen_completionRecord_eq {a : Pattern} {rec : Records} {r y : Nat}
    (processed : List Nat) {xs : List Nat}
    (old : computeMarkTrace a r y = some xs)
    (current : computeMarkTrace (processed.foldl (fun current z => completeMark current rec r z) a) r y = some xs)
    (below : ∀ i ∈ xs.dropLast, i < r) :
    completionRecord (processed.foldl (fun current z => completeMark current rec r z) a) rec r y =
      completionRecord a rec r y := by
  simp only [completionRecord, old, current]
  dsimp only [Bind.bind, Option.bind]
  rw [frozen_currentPlusOne_eq processed below]

end FullMarkedBLP


