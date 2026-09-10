import FullMarkedBLP.CopyMiddleBridge

namespace FullMarkedBLP

/-- Exact middle-splice word: the translated high prefix, followed by the
parent last-row marked bridge, followed by the unchanged low tail. -/
theorem shortCopy_middle_word {a b : Pattern} {last : Row}
    {p e minimum low shifted s y s' y' : Nat} {xs bridge : List Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (copy : shortCopy a = some b) (lastAt : a.getLast? = some last)
    (hp : last.p = some p) (he : last.e = some e)
    (minimumAt : last.core.head? = some minimum) (lowAbove : minimum ≤ low)
    (sourceBelow : s < minimum) (headBound : y < e) (hpn : p ≤ a.length)
    (lastValid : last.CoreValid a.length) (trace : Trace a s y xs)
    (firstLow : xs.find? (· < p) = some low)
    (sourceMap : copyEntry a.length last s = some s')
    (targetMap : copyEntry a.length last y = some y')
    (lowMap : copyEntry a.length last low = some shifted)
    (bridgeTrace : Trace a low shifted bridge) (bridgeBound : shifted < a.length) :
    ∃ front tail, xs = front ++ tail ∧ Trace a s low tail ∧ tail.dropLast ≠ [] ∧
      (∀ v ∈ front, p ≤ v) ∧
      Trace b s' y' (front.map (fun v => v + (a.length - p)) ++ (bridge.dropLast ++ tail)) := by
  have sourceEq := copyEntry_low_value minimumAt sourceBelow sourceMap
  induction trace generalizing y' with
  | stop =>
    have same : low = s := List.mem_singleton.mp (List.mem_of_find?_eq_some firstLow)
    omega
  | @next y z rest sourceLt predecessorAt trace ih =>
    by_cases headLow : y < p
    · have headEq : y = low := by simpa [List.find?_cons, headLow] using firstLow
      have targetEq : y' = shifted := Option.some.inj ((headEq ▸ targetMap).symm.trans lowMap)
      have tailTrace : Trace a s low (y :: rest) := by simpa only [headEq] using Trace.next sourceLt predecessorAt trace
      have nonempty : (y :: rest).dropLast ≠ [] := by
        cases rest with
        | nil => exact False.elim (trace_nonempty trace rfl)
        | cons v tail => simp
      refine ⟨[], y :: rest, rfl, tailTrace, nonempty, by simp, ?_⟩
      have joined := trace_join (shortCopy_prefix_trace valid copy bridgeTrace bridgeBound)
        (shortCopy_prefix_trace valid copy tailTrace (by omega))
      simpa only [List.map_nil, List.nil_append, sourceEq, targetEq] using joined
    · have firstLow' : rest.find? (· < p) = some low := by
        simpa [List.find?_cons, headLow] using firstLow
      have high : p ≤ y := by omega
      obtain ⟨z', zMap, copiedPredecessor⟩ := shortCopy_predecessor copy lastAt hp he high headBound hpn predecessorAt
      have targetEq := copyEntry_high_value lastValid hp high targetMap
      have newPredecessor : predecessor b y' = some z' := by simpa only [targetEq] using copiedPredecessor
      have smaller := predecessor_lt valid predecessorAt
      obtain ⟨front, tail, shape, tailTrace, nonempty, allHigh, newTrace⟩ :=
        ih (by omega) firstLow' zMap
      refine ⟨y :: front, tail, ?_, tailTrace, nonempty, ?_, ?_⟩
      · simpa only [List.cons_append] using congrArg (List.cons y) shape
      · intro v hv
        rcases List.mem_cons.mp hv with same | inside
        · omega
        · exact allHigh v inside
      · simpa only [List.map_cons, List.cons_append, ← targetEq] using
          Trace.next (copyEntry_strict lastValid sourceLt sourceMap targetMap) newPredecessor newTrace

end FullMarkedBLP
