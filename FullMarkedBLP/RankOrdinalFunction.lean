import FullMarkedBLP.RankFunctionSpace
import FullMarkedBLP.OrdinalAction

namespace FullMarkedBLP
open FirstOrder Language

/-- A set function with ordinal values, bounded by an ordinal in the same
rank domain. The domain of the function need not be an ordinal. -/
def RankOrdinalFunction {lambda : Ordinal.{u}} (f : RankDomain lambda) : Prop :=
  ∃ domain range : RankDomain lambda, rankIsFunction f domain range ∧ ZFSet.IsOrdinal range.val

def rankOrdinalAt {alpha : Type} {n : Nat} (x : alpha ⊕ Fin n) :
    membershipLanguage.BoundedFormula alpha n :=
  BoundedFormula.relabel ![x] rankOrdinalFormula

theorem rankOrdinalAt_realize {lambda : Ordinal.{u}} {alpha : Type} {n : Nat}
    (x : alpha ⊕ Fin n) (v : alpha → RankDomain lambda) (xs : Fin n → RankDomain lambda) :
    (rankOrdinalAt x).Realize v xs ↔ ZFSet.IsOrdinal (Sum.elim v xs x).val := by
  simp only [rankOrdinalAt, BoundedFormula.realize_relabel]
  change rankOrdinalFormula.Realize (Sum.elim v xs ∘ ![x]) ↔ _
  have same : Sum.elim v xs ∘ ![x] = ![Sum.elim v xs x] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [same]
  exact rankOrdinalFormula_realize _

def rankOrdinalFunctionFormula : membershipLanguage.Formula (Fin 1) :=
  .ex (.ex ((rankFunctionAt (.inl 0) (.inr 0) (.inr 1)) ⊓ rankOrdinalAt (.inr 1)))

theorem rankOrdinalFunctionFormula_realize {lambda : Ordinal.{u}} (f : RankDomain lambda) :
    rankOrdinalFunctionFormula.Realize ![f] ↔ RankOrdinalFunction f := by
  simp [rankOrdinalFunctionFormula, Formula.Realize, BoundedFormula.Realize,
    rankFunctionAt_realize, rankOrdinalAt_realize, RankOrdinalFunction, Fin.snoc]

theorem rankElementary_ordinalFunction_iff {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (f : RankDomain lambda) :
    RankOrdinalFunction (j f) ↔ RankOrdinalFunction f := by
  have result := j.map_formula rankOrdinalFunctionFormula ![f]
  have same : j ∘ ![f] = ![j f] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [same, rankOrdinalFunctionFormula_realize, rankOrdinalFunctionFormula_realize] at result
  exact result

theorem rankOrdinalFunction_unique {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {f a b c : RankDomain lambda} (function : RankOrdinalFunction f)
    (hb : rankGraphApplies f a b) (hc : rankGraphApplies f a c) : b = c := by
  obtain ⟨domain, range, hf, _⟩ := function
  have pair := (rankGraphApplies_iff hl _ _ _).mp hb
  have member := (ZFSet.pair_mem_prod.mp (((rankIsFunction_iff hl _ _ _).mp hf).1 pair)).1
  obtain ⟨value, _, _, unique⟩ := hf.2 a member
  exact (unique _ hb).trans (unique _ hc).symm

theorem rankOrdinalFunction_value {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {f a : RankDomain lambda} {b : ZFSet.{u}} (function : RankOrdinalFunction f)
    (edge : ZFSet.pair a.val b ∈ f.val) : ZFSet.IsOrdinal b := by
  obtain ⟨domain, range, hf, ordinal⟩ := function
  exact ordinal.mem (ZFSet.pair_mem_prod.mp (((rankIsFunction_iff hl _ _ _).mp hf).1 edge)).2

/-- The value of any graph edge has smaller rank than the graph. -/
theorem rank_graph_value_lt {f a b : ZFSet.{u}} (edge : ZFSet.pair a b ∈ f) : b.rank < f.rank := by
  have pairMember : ({a, b} : ZFSet) ∈ ZFSet.pair a b := ZFSet.mem_pair.mpr (Or.inr rfl)
  have valueMember : b ∈ ({a, b} : ZFSet) := ZFSet.mem_pair.mpr (Or.inr rfl)
  exact (ZFSet.rank_lt_of_mem valueMember).trans
    ((ZFSet.rank_lt_of_mem pairMember).trans (ZFSet.rank_lt_of_mem edge))

end FullMarkedBLP
