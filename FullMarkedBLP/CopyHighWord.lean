import FullMarkedBLP.CopyTerminalTrace

namespace FullMarkedBLP

/-- In the all-high case, identify the entire factor word, retaining the
actual copied endpoint even when that endpoint lies below the threshold. -/
theorem shortCopy_high_terminal_word {a b : Pattern} {last : Row}
    {p e s y terminal s' y' : Nat} {xs : List Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (copy : shortCopy a = some b) (lastAt : a.getLast? = some last)
    (hp : last.p = some p) (he : last.e = some e)
    (hpt : p ≤ terminal) (hye : y < e) (hpn : p ≤ a.length)
    (lastValid : last.CoreValid a.length) (trace : Trace a s y xs)
    (terminalAt : fromRight xs 2 = some terminal)
    (sourceMap : copyEntry a.length last s = some s')
    (targetMap : copyEntry a.length last y = some y') :
    Trace b s' y' (xs.dropLast.map (fun v => v + (a.length - p)) ++ [s']) := by
  induction trace generalizing y' with
  | stop => simp [fromRight] at terminalAt
  | @next y z tail sourceLt predecessorAt trace ih =>
    have terminalBound := (trace_terminal_factor valid (Trace.next sourceLt predecessorAt trace) terminalAt).2.2
    have high : p ≤ y := by omega
    have targetEq := copyEntry_high_value lastValid hp high targetMap
    obtain ⟨z', zMap, predecessorCopy⟩ := shortCopy_predecessor copy lastAt hp he high hye hpn predecessorAt
    have newPredecessor : predecessor b y' = some z' := by simpa only [targetEq] using predecessorCopy
    have strict := copyEntry_strict lastValid sourceLt sourceMap targetMap
    cases tail with
    | nil => exact False.elim (trace_nonempty trace rfl)
    | cons v rest =>
      cases rest with
      | nil =>
        have vz : v = z := by simpa using trace_head trace
        have vs : v = s := by simpa using trace_last trace
        have zs : z = s := vz.symm.trans vs
        have endpointEq : z' = s' := Option.some.inj ((zs ▸ zMap).symm.trans sourceMap)
        subst z'
        simpa only [List.dropLast_cons_cons, List.dropLast_singleton, List.map_cons,
          List.map_nil, List.cons_append, List.nil_append, ← targetEq] using
          (Trace.next strict newPredecessor Trace.stop : Trace b s' y' [y', s'])
      | cons w rest =>
        have terminalAt' : fromRight (v :: w :: rest) 2 = some terminal := by
          simpa only [fromRight_cons_of_le (by simp : 2 ≤ (v :: w :: rest).length)] using terminalAt
        have zy := predecessor_lt valid predecessorAt
        have result := ih (by omega) terminalAt' zMap
        simpa only [List.dropLast_cons_cons, List.map_cons, List.cons_append, ← targetEq] using
          Trace.next strict newPredecessor result

end FullMarkedBLP
