import FullMarkedBLP.RankHierarchyImage
import FullMarkedBLP.RankApplicationComposition

namespace FullMarkedBLP
open FirstOrder Language

/-- Weak membership agreement for two set graphs on a set cutoff. -/
def RankGraphsWeakAgreement {lambda : Ordinal.{u}} (left right cutoff : RankDomain lambda) : Prop :=
  ∀ x z p q : RankDomain lambda, x.val ∈ cutoff.val → z.val ∈ cutoff.val →
    rankGraphApplies left z p → rankGraphApplies right z q → (x.val ∈ p.val ↔ x.val ∈ q.val)

def rankGraphsWeakAgreementFormula : membershipLanguage.Formula (Fin 3) :=
  .all (.all (.all (.all ((rankMemAt (.inr 0) (.inl 2)).imp
    ((rankMemAt (.inr 1) (.inl 2)).imp
      ((rankGraphAppliesAt (.inl 0) (.inr 1) (.inr 2)).imp
        ((rankGraphAppliesAt (.inl 1) (.inr 1) (.inr 3)).imp
          ((rankMemAt (.inr 0) (.inr 2)).iff (rankMemAt (.inr 0) (.inr 3))))))))))

theorem rankGraphsWeakAgreementFormula_realize {lambda : Ordinal.{u}}
    (left right cutoff : RankDomain lambda) :
    rankGraphsWeakAgreementFormula.Realize ![left, right, cutoff] ↔ RankGraphsWeakAgreement left right cutoff := by
  simp [rankGraphsWeakAgreementFormula, RankGraphsWeakAgreement, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_iff, rankMemAt_realize, rankGraphAppliesAt_realize, Fin.snoc]

theorem rankElementary_graphsWeakAgreement_iff {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    (left right cutoff : RankDomain lambda) :
    RankGraphsWeakAgreement (j left) (j right) (j cutoff) ↔ RankGraphsWeakAgreement left right cutoff := by
  have result := j.map_formula rankGraphsWeakAgreementFormula ![left, right, cutoff]
  have same : j ∘ ![left, right, cutoff] = ![j left, j right, j cutoff] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  rw [same, rankGraphsWeakAgreementFormula_realize, rankGraphsWeakAgreementFormula_realize] at result
  exact result

theorem rankRestrictionGraphs_weakAgreement {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {left right : RankElementaryEmbedding lambda} {delta : OrdinalDomain lambda}
    (agreement : rankCutoffAgreement delta.val left right) :
    RankGraphsWeakAgreement (rankRestrictionGraph hl left (rankHierarchy delta))
      (rankRestrictionGraph hl right (rankHierarchy delta)) (rankHierarchy delta) := by
  intro x z p q hx hz leftEdge rightEdge
  have leftEq := ((rankRestrictionGraph_applies_iff hl left _ z p).mp leftEdge).2
  have rightEq := ((rankRestrictionGraph_applies_iff hl right _ z q).mp rightEdge).2
  rw [← leftEq, ← rightEq]
  exact agreement x z (ZFSet.mem_vonNeumann.mp hx) (ZFSet.mem_vonNeumann.mp hz)

/-- The manuscript's weak rank-cutoff agreement is preserved by genuine
application, at the exact image cutoff. No equality of function values
below the original cutoff is assumed. -/
theorem rankApply_cutoffAgreement {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (outer : RankElementaryEmbedding lambda) {left right : RankElementaryEmbedding lambda}
    {delta : OrdinalDomain lambda} (agreement : rankCutoffAgreement delta.val left right) :
    rankCutoffAgreement (rankOrdinalAction outer delta).val (rankApply hl outer left) (rankApply hl outer right) := by
  have transferred := (rankElementary_graphsWeakAgreement_iff outer _ _ _).mpr
    (rankRestrictionGraphs_weakAgreement hl agreement)
  intro x z hx hz
  have xMember : x.val ∈ (outer (rankHierarchy delta)).val := by
    rw [rankElementary_hierarchy hl outer delta]
    exact ZFSet.mem_vonNeumann.mpr hx
  have zMember : z.val ∈ (outer (rankHierarchy delta)).val := by
    rw [rankElementary_hierarchy hl outer delta]
    exact ZFSet.mem_vonNeumann.mpr hz
  have leftEdge := rankApplication_on_domain hl outer left (rankElementary_image_cofinal hl outer)
    (rankHierarchy delta) z zMember
  have rightEdge := rankApplication_on_domain hl outer right (rankElementary_image_cofinal hl outer)
    (rankHierarchy delta) z zMember
  exact transferred x z (rankApply hl outer left z) (rankApply hl outer right z) xMember zMember leftEdge rightEdge

end FullMarkedBLP
