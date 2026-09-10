import FullMarkedBLP.RankFunctionFormula
import FullMarkedBLP.ZFFunctionEquiv

namespace FullMarkedBLP
open FirstOrder Language

theorem rank_funs_lt_of_limit {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {x y : ZFSet.{u}} (hx : x.rank < lambda) (hy : y.rank < lambda) :
    (ZFSet.funs x y).rank < lambda := by
  have included : ZFSet.funs x y ⊆ ZFSet.powerset (ZFSet.prod x y) := by
    intro f hf
    exact ZFSet.mem_powerset.mpr (ZFSet.mem_funs.mp hf).1
  apply (ZFSet.rank_mono included).trans_lt
  rw [ZFSet.rank_powerset]
  exact hl.succ_lt (rank_graph_lt_of_limit hl hx hy (fun _ h => h))

noncomputable def rankFunctionSpace {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (x y : RankDomain lambda) : RankDomain lambda :=
  ⟨ZFSet.funs x.val y.val, rank_funs_lt_of_limit hl x.property y.property⟩

def rankFunctionAt {alpha : Type} {n : Nat} (f x y : alpha ⊕ Fin n) :
    membershipLanguage.BoundedFormula alpha n :=
  BoundedFormula.relabel ![f, x, y] rankFunctionFormula

theorem rankFunctionAt_realize {lambda : Ordinal.{u}} {alpha : Type} {n : Nat}
    (f x y : alpha ⊕ Fin n) (v : alpha → RankDomain lambda) (xs : Fin n → RankDomain lambda) :
    (rankFunctionAt f x y).Realize v xs ↔
      rankIsFunction (Sum.elim v xs f) (Sum.elim v xs x) (Sum.elim v xs y) := by
  simp only [rankFunctionAt, BoundedFormula.realize_relabel]
  change rankFunctionFormula.Realize (Sum.elim v xs ∘ ![f, x, y]) ↔ _
  have same : Sum.elim v xs ∘ ![f, x, y] =
      ![Sum.elim v xs f, Sum.elim v xs x, Sum.elim v xs y] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  rw [same]
  exact rankFunctionFormula_realize _ _ _

def rankFunctionSpaceFormula : membershipLanguage.Formula (Fin 3) :=
  .all ((rankMemAt (.inr 0) (.inl 0)).iff
    (rankFunctionAt (.inr 0) (.inl 1) (.inl 2)))

theorem rankFunctionSpaceFormula_realize {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (p x y : RankDomain lambda) :
    rankFunctionSpaceFormula.Realize ![p, x, y] ↔ p = rankFunctionSpace hl x y := by
  have semantics : rankFunctionSpaceFormula.Realize ![p, x, y] ↔
      ∀ f : RankDomain lambda, f.val ∈ p.val ↔ rankIsFunction f x y := by
    simp [rankFunctionSpaceFormula, Formula.Realize,
      rankMemAt_realize, rankFunctionAt_realize, Fin.snoc]
  rw [semantics]
  constructor
  · intro h
    apply Subtype.ext
    apply ZFSet.ext
    intro f
    constructor
    · intro member
      exact ZFSet.mem_funs.mpr ((rankIsFunction_iff hl _ _ _).mp ((h (rankMember p f member)).mp member))
    · intro member
      have function := ZFSet.mem_funs.mp member
      let graph : RankDomain lambda := ⟨f, rank_function_lt_of_limit hl x.property y.property function⟩
      exact (h graph).mpr ((rankIsFunction_iff hl _ _ _).mpr function)
  · intro same f
    rw [same]
    exact ZFSet.mem_funs.trans (rankIsFunction_iff hl f x y).symm

theorem rankElementary_functionSpace {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (x y : RankDomain lambda) :
    j (rankFunctionSpace hl x y) = rankFunctionSpace hl (j x) (j y) := by
  have result := j.map_formula rankFunctionSpaceFormula ![rankFunctionSpace hl x y, x, y]
  have same : j ∘ ![rankFunctionSpace hl x y, x, y] = ![j (rankFunctionSpace hl x y), j x, j y] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  rw [same, rankFunctionSpaceFormula_realize hl, rankFunctionSpaceFormula_realize hl] at result
  exact result.mpr rfl

end FullMarkedBLP
