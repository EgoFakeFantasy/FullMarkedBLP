import FullMarkedBLP.RankNontrivialFormula

namespace FullMarkedBLP

def rankFormulaClassEqual {m n : Nat} (left right : Fin m) : RankPredicateFormula m n :=
  .all ((RankPredicateFormula.predicate left (Fin.last n)).iff (.predicate right (Fin.last n)))

theorem rankFormulaClassEqual_realize {lambda : Ordinal.{u}} {m n : Nat} (left right : Fin m)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda) :
    (rankFormulaClassEqual (n := n) left right).Realize classes values ↔ classes left = classes right := by
  simp only [rankFormulaClassEqual, RankPredicateFormula.Realize, RankPredicateFormula.realize_iff,
    Fin.snoc_last]
  exact ⟨fun h => funext (fun x => propext (h x)), fun h x => by rw [h]⟩

def rankFormulaFiniteAnd {m n : Nat} : {k : Nat} → (Fin k → RankPredicateFormula m n) → RankPredicateFormula m n
  | 0, _ => .imp .falsum .falsum
  | k + 1, clauses => (clauses 0).and (rankFormulaFiniteAnd (fun i : Fin k => clauses i.succ))

theorem rankFormulaFiniteAnd_realize {lambda : Ordinal.{u}} {m n k : Nat}
    (clauses : Fin k → RankPredicateFormula m n) (classes : Fin m → RankClass lambda)
    (values : Fin n → RankDomain lambda) :
    (rankFormulaFiniteAnd clauses).Realize classes values ↔ ∀ i, (clauses i).Realize classes values := by
  induction k with
  | zero => exact ⟨fun _ i => Fin.elim0 i, fun _ => id⟩
  | succ k ih =>
    rw [rankFormulaFiniteAnd, RankPredicateFormula.realize_and, ih]
    exact ⟨fun h i => Fin.cases h.1 h.2 i, fun h => ⟨h 0, fun i => h i.succ⟩⟩

end FullMarkedBLP
