import FullMarkedBLP.CopyLowTrace

namespace FullMarkedBLP

/-- Recover the exact high prefix and nonempty low factor tail in the
literal low retention branch. The low tail, including its endpoint, stays
unchanged in the copied pattern. -/
theorem shortCopy_low_word {a b : Pattern} {last : Row}
    {p e minimum low s y s' y' terminal : Nat} {xs : List Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (copy : shortCopy a = some b) (lastAt : a.getLast? = some last)
    (hp : last.p = some p) (he : last.e = some e)
    (minimumAt : last.core.head? = some minimum) (lowBelow : low < minimum)
    (headBound : y < e) (hpn : p ≤ a.length) (lastValid : last.CoreValid a.length)
    (trace : Trace a s y xs) (firstLow : xs.find? (· < p) = some low)
    (terminalAt : fromRight xs 2 = some terminal) (terminalLow : terminal < p)
    (sourceMap : copyEntry a.length last s = some s')
    (targetMap : copyEntry a.length last y = some y') :
    ∃ front tail, xs = front ++ tail ∧ Trace a s low tail ∧ tail.dropLast ≠ [] ∧
      (∀ v ∈ front, p ≤ v) ∧ s' = s ∧
      Trace b s' y' (front.map (fun v => v + (a.length - p)) ++ tail) := by
  induction trace generalizing y' with
  | stop => simp [fromRight] at terminalAt
  | @next y z rest sourceLt predecessorAt trace ih =>
    by_cases headLow : y < p
    · have headEq : y = low := by simpa [List.find?_cons, headLow] using firstLow
      have targetEq := copyEntry_low_value minimumAt (by omega : y < minimum) targetMap
      have sourceEq := copyEntry_low_value minimumAt (by omega : s < minimum) sourceMap
      have nonempty : (y :: rest).dropLast ≠ [] := by
        cases rest with
        | nil => exact False.elim (trace_nonempty trace rfl)
        | cons v tail => simp
      refine ⟨[], y :: rest, rfl, ?_, nonempty, by simp, sourceEq, ?_⟩
      · simpa only [headEq] using Trace.next sourceLt predecessorAt trace
      · simpa only [List.map_nil, List.nil_append, targetEq, sourceEq] using
          shortCopy_prefix_trace valid copy (Trace.next sourceLt predecessorAt trace) (by omega)
    · have high : p ≤ y := by omega
      have firstLow' : rest.find? (· < p) = some low := by
        simpa [List.find?_cons, headLow] using firstLow
      cases rest with
      | nil => exact False.elim (trace_nonempty trace rfl)
      | cons v tail =>
        cases tail with
        | nil =>
          have same : y = terminal := by simpa [fromRight] using terminalAt
          omega
        | cons w tail =>
          have terminalAt' : fromRight (v :: w :: tail) 2 = some terminal := by
            simpa only [fromRight_cons_of_le (by simp : 2 ≤ (v :: w :: tail).length)] using terminalAt
          obtain ⟨z', zMap, copiedPredecessor⟩ :=
            shortCopy_predecessor copy lastAt hp he high headBound hpn predecessorAt
          have targetEq := copyEntry_high_value lastValid hp high targetMap
          have newPredecessor : predecessor b y' = some z' := by simpa only [targetEq] using copiedPredecessor
          have smaller := predecessor_lt valid predecessorAt
          obtain ⟨front, rest', shape, tailTrace, nonempty, allHigh, sourceEq, copiedTrace⟩ :=
            ih (by omega) firstLow' terminalAt' zMap
          refine ⟨y :: front, rest', ?_, tailTrace, nonempty, ?_, sourceEq, ?_⟩
          · simpa only [List.cons_append] using congrArg (List.cons y) shape
          · intro v hv
            rcases List.mem_cons.mp hv with same | inside
            · omega
            · exact allHigh v inside
          · simpa only [List.map_cons, List.cons_append, ← targetEq] using
              Trace.next (copyEntry_strict lastValid sourceLt sourceMap targetMap) newPredecessor copiedTrace

end FullMarkedBLP
