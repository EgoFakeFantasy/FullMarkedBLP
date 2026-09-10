import FullMarkedBLP.Trace

namespace FullMarkedBLP

/-- An actual trace is unique even before a semantic certificate is supplied. -/
theorem trace_unique {a : Pattern} {s y : Nat} {xs ys : List Nat}
    (h : Trace a s y xs) (g : Trace a s y ys) : xs = ys := by
  induction h generalizing ys with
  | stop =>
    cases g with
    | stop => rfl
    | next hlt _ _ => exact False.elim (Nat.lt_irrefl _ hlt)
  | next hlt hp ht ih =>
    cases g with
    | stop => exact False.elim (Nat.lt_irrefl _ hlt)
    | next _ hp' ht' =>
      have heq := Option.some.inj (hp.symm.trans hp')
      subst heq
      exact congrArg _ (ih ht')

/-- Terminal p-chain source is the last entry of the actual trace. -/
theorem trace_last {a : Pattern} {s y : Nat} {xs : List Nat}
    (h : Trace a s y xs) : xs.getLast? = some s := by
  induction h with
  | stop => rfl
  | next _ _ ht ih =>
    cases ht with
    | stop => exact ih
    | next _ _ _ => exact ih

#print axioms trace_unique
#print axioms trace_last
#print axioms start_mark_trace

end FullMarkedBLP
