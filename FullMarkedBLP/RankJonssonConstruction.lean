import FullMarkedBLP.RankSequenceGraph
import FullMarkedBLP.RankJonssonFormula
import FullMarkedBLP.CardinalOmegaJonsson

namespace FullMarkedBLP

/-- Turn an externally constructed omega-Jonsson coloring into its actual
set graph and prove its first-order Jonsson property in the rank domain. -/
theorem rankJonssonGraph_exists {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (target : RankDomain lambda)
    (color : (Nat → target.val) → target.val) (jonsson : IsOmegaJonsson color) :
    ∃ graph : RankDomain lambda,
      rankIsFunction graph (rankFunctionSpace hl (ordinalDomainElement ⟨Ordinal.omega0, hw⟩) target) target ∧
      RankGraphOmegaJonsson graph (ordinalDomainElement ⟨Ordinal.omega0, hw⟩) target := by
  classical
  let omega := ordinalDomainElement (⟨Ordinal.omega0, hw⟩ : OrdinalDomain lambda)
  let space := rankFunctionSpace hl omega target
  let function : space.val → target.val := fun sequence => color ((zfSequenceEquiv target.val).symm sequence)
  let graph := rankFunctionGraph hl space target function
  refine ⟨graph, rankFunctionGraph_isFunction hl space target function, ?_⟩
  intro A included bijection bijective value hv
  let inclusion : A.val → target.val := fun a => ⟨a.val, included a.property⟩
  have inclusionInj : Function.Injective inclusion := by
    intro a b same
    exact Subtype.ext (congrArg (fun b : target.val => b.val) same)
  have sameCard : Cardinal.mk (Set.range inclusion) = Cardinal.mk target.val := by
    rw [Cardinal.mk_range_eq inclusion inclusionInj]
    rw [ZFSet.cardinalMk_coe_sort, ZFSet.cardinalMk_coe_sort,
      (rankBijection_card_eq hl bijective).symm]
  obtain ⟨sequence, allInside, colored⟩ := jonsson (Set.range inclusion) sameCard ⟨value.val, hv⟩
  have insideA : ∀ n, (sequence n).val ∈ A.val := by
    intro n
    obtain ⟨a, ha⟩ := allInside n
    have same : a.val = (sequence n).val := congrArg Subtype.val ha
    exact same ▸ a.property
  let sequenceA : Nat → A.val := fun n => ⟨(sequence n).val, insideA n⟩
  let sequenceGraph := rankSequenceGraph hl hw target sequence
  have inA : rankIsFunction sequenceGraph omega A := by
    have same := rankSequenceGraph_congr hl hw target A sequence sequenceA (fun _ => rfl)
    change rankIsFunction (rankSequenceGraph hl hw target sequence) omega A
    rw [same]
    exact rankSequenceGraph_isFunction hl hw A sequenceA
  refine ⟨sequenceGraph, inA, ?_⟩
  apply (rankGraphApplies_iff hl _ _ _).mpr
  apply (mem_zfFunctionGraph function _ _).mpr
  have member : sequenceGraph.val ∈ space.val :=
    ZFSet.mem_funs.mpr ((rankIsFunction_iff hl _ _ _).mp (rankSequenceGraph_isFunction hl hw target sequence))
  refine ⟨member, ?_⟩
  change (color ((zfSequenceEquiv target.val).symm (zfSequenceEquiv target.val sequence))).val = value.val
  rw [Equiv.symm_apply_apply]
  exact congrArg Subtype.val colored

end FullMarkedBLP
