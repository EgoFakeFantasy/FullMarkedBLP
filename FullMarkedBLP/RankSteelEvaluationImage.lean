import FullMarkedBLP.RankSteelEvaluation

namespace FullMarkedBLP
open FirstOrder Language

def RankSteelEvaluationDescribes {lambda : Ordinal.{u}} (graph level restriction : RankDomain lambda) : Prop :=
  ∀ input value : RankDomain lambda, rankGraphApplies graph input value ↔
    ∃ f s output : RankDomain lambda, f.val ∈ level.val ∧ s.val ∈ level.val ∧
      RankOrdinalFunction f ∧ rankIsOrderedPair input f s ∧
      rankGraphApplies restriction f output ∧ rankGraphApplies output s value

def rankSteelEvaluationFormula : membershipLanguage.Formula (Fin 3) :=
  .all (.all ((rankGraphAppliesAt (.inl 0) (.inr 0) (.inr 1)).iff
    (.ex (.ex (.ex ((rankMemAt (.inr 2) (.inl 1)) ⊓
      ((rankMemAt (.inr 3) (.inl 1)) ⊓ ((rankOrdinalFunctionAt (.inr 2)) ⊓
        ((rankOrderedPairAt (.inr 0) (.inr 2) (.inr 3)) ⊓
          ((rankGraphAppliesAt (.inl 2) (.inr 2) (.inr 4)) ⊓
            rankGraphAppliesAt (.inr 4) (.inr 3) (.inr 1)))))))))))

theorem rankSteelEvaluationFormula_realize {lambda : Ordinal.{u}} (graph level restriction : RankDomain lambda) :
    rankSteelEvaluationFormula.Realize ![graph, level, restriction] ↔
      RankSteelEvaluationDescribes graph level restriction := by
  simp [rankSteelEvaluationFormula, Formula.Realize, BoundedFormula.Realize,
    rankMemAt_realize, rankOrdinalFunctionAt_realize, rankOrderedPairAt_realize,
    rankGraphAppliesAt_realize, RankSteelEvaluationDescribes, Fin.snoc]

theorem rankElementary_evaluationDescribes_iff {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (graph level restriction : RankDomain lambda) :
    RankSteelEvaluationDescribes (j graph) (j level) (j restriction) ↔
      RankSteelEvaluationDescribes graph level restriction := by
  have result := j.map_formula rankSteelEvaluationFormula ![graph, level, restriction]
  have same : j ∘ ![graph, level, restriction] = ![j graph, j level, j restriction] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  rw [same, rankSteelEvaluationFormula_realize, rankSteelEvaluationFormula_realize] at result
  exact result

theorem rankSteelEvaluation_describes_of_restriction {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) (restriction : RankDomain lambda)
    (describes : ∀ f output : RankDomain lambda, rankGraphApplies restriction f output ↔
      f.val ∈ (rankHierarchy alpha).val ∧ k f = output) :
    RankSteelEvaluationDescribes (rankSteelEvaluationGraph hl k alpha) (rankHierarchy alpha) restriction := by
  intro input value
  rw [rankSteelEvaluationGraph_applies_iff]
  constructor
  · rintro ⟨f, s, hf, hs, function, pair, edge⟩
    have member := ZFSet.mem_vonNeumann.mpr hf
    exact ⟨f, s, k f, member, ZFSet.mem_vonNeumann.mpr hs, function,
      (rankIsOrderedPair_iff hl _ _ _).mpr pair,
      (describes f (k f)).mpr ⟨member, rfl⟩, (rankGraphApplies_iff hl _ _ _).mpr edge⟩
  · rintro ⟨f, s, output, hf, hs, function, pair, restricted, edge⟩
    have same := ((describes f output).mp restricted).2
    refine ⟨f, s, ZFSet.mem_vonNeumann.mp hf, ZFSet.mem_vonNeumann.mp hs, function,
      (rankIsOrderedPair_iff hl _ _ _).mp pair, ?_⟩
    rw [same]
    exact (rankGraphApplies_iff hl _ _ _).mp edge

theorem rankSteelEvaluation_describes {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    RankSteelEvaluationDescribes (rankSteelEvaluationGraph hl k alpha) (rankHierarchy alpha)
      (rankRestrictionGraph hl k (rankHierarchy alpha)) :=
  rankSteelEvaluation_describes_of_restriction hl k alpha _ (rankRestrictionGraph_applies_iff hl k _)

/-- Transfer of the actual evaluation graph on every input of the image
level. This is the G equation in Steel's order-collapse argument. -/
theorem rankElementary_steelEvaluation_applies_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) (input value : RankDomain lambda) :
    rankGraphApplies (j (rankSteelEvaluationGraph hl k alpha)) input value ↔
      RankSteelEvaluates (rankApply hl j k) (rankOrdinalAction j alpha) input.val value.val := by
  have image := (rankElementary_evaluationDescribes_iff j _ _ _).mpr (rankSteelEvaluation_describes hl k alpha)
  rw [rankElementary_hierarchy hl] at image
  have restriction : ∀ f output : RankDomain lambda,
      rankGraphApplies (j (rankRestrictionGraph hl k (rankHierarchy alpha))) f output ↔
        f.val ∈ (rankHierarchy (rankOrdinalAction j alpha)).val ∧ rankApply hl j k f = output := by
    intro f output
    have exactRestriction := rankApply_restriction_applies_iff hl j k (rankHierarchy alpha) f output
    rw [rankElementary_hierarchy hl] at exactRestriction
    exact exactRestriction
  have other := rankSteelEvaluation_describes_of_restriction hl (rankApply hl j k)
    (rankOrdinalAction j alpha) _ restriction
  exact ((image input value).trans (other input value).symm).trans
    (rankSteelEvaluationGraph_applies_iff hl _ _ input value)

end FullMarkedBLP
