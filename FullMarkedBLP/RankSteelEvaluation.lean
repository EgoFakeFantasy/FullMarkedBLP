import FullMarkedBLP.RankSteelHullImage
import FullMarkedBLP.RankSequenceGraph
import FullMarkedBLP.RankCriticalStrongLimit

namespace FullMarkedBLP

/-- The partial evaluation used in Steel's proof, with input the ordered
pair of a low-rank ordinal-valued function and a low-rank argument. -/
def RankSteelEvaluates {lambda : Ordinal.{u}} (k : RankElementaryEmbedding lambda)
    (alpha : OrdinalDomain lambda) (input value : ZFSet.{u}) : Prop :=
  ∃ f s : RankDomain lambda, f.val.rank < alpha.val ∧ s.val.rank < alpha.val ∧
    RankOrdinalFunction f ∧ input = ZFSet.pair f.val s.val ∧ ZFSet.pair s.val value ∈ (k f).val

theorem rankSteelEvaluates_unique {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) {input a b : ZFSet.{u}}
    (left : RankSteelEvaluates k alpha input a) (right : RankSteelEvaluates k alpha input b) : a = b := by
  obtain ⟨f, s, _, _, function, eq, edge⟩ := left
  obtain ⟨g, t, _, _, _, eq', edge'⟩ := right
  obtain ⟨sameF, sameS⟩ := ZFSet.pair_inj.mp (eq.symm.trans eq')
  have fg : f = g := Subtype.ext sameF
  have st : s = t := Subtype.ext sameS
  rw [← fg, ← st] at edge'
  have mapped := (rankElementary_ordinalFunction_iff k f).mpr function
  let a' : RankDomain lambda := ⟨a, (rank_graph_value_lt edge).trans (k f).property⟩
  let b' : RankDomain lambda := ⟨b, (rank_graph_value_lt edge').trans (k f).property⟩
  exact congrArg Subtype.val (rankOrdinalFunction_unique hl mapped
    ((rankGraphApplies_iff hl (k f) s a').mpr edge) ((rankGraphApplies_iff hl (k f) s b').mpr edge'))

theorem rankSteelEvaluates_input {lambda : Ordinal.{u}}
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) {input value : ZFSet.{u}}
    (evaluates : RankSteelEvaluates k alpha input value) :
    input ∈ ZFSet.prod (rankHierarchy alpha).val (rankHierarchy alpha).val := by
  obtain ⟨f, s, hf, hs, _, rfl, _⟩ := evaluates
  exact ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_vonNeumann.mpr hf, ZFSet.mem_vonNeumann.mpr hs⟩

theorem rankSteelEvaluates_value {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) {input value : ZFSet.{u}}
    (evaluates : RankSteelEvaluates k alpha input value) : value ∈ (rankSteelHull hl k alpha).val := by
  obtain ⟨f, s, hf, hs, function, _, edge⟩ := evaluates
  exact (rankSteelHull_mem hl k alpha value).mpr ⟨f, s, hf, hs, function, edge⟩

noncomputable def rankSteelEvaluationDomain {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) : RankDomain lambda :=
  ⟨ZFSet.sep (fun input => ∃ value, RankSteelEvaluates k alpha input value)
    (ZFSet.prod (rankHierarchy alpha).val (rankHierarchy alpha).val), by
      apply rank_graph_lt_of_limit hl (rankHierarchy alpha).property (rankHierarchy alpha).property
      exact fun _ h => (ZFSet.mem_sep.mp h).1⟩

theorem rankSteelEvaluationDomain_mem {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) (input : ZFSet.{u}) :
    input ∈ (rankSteelEvaluationDomain hl k alpha).val ↔ ∃ value, RankSteelEvaluates k alpha input value := by
  change input ∈ ZFSet.sep (fun p => ∃ value, RankSteelEvaluates k alpha p value)
    (ZFSet.prod (rankHierarchy alpha).val (rankHierarchy alpha).val) ↔ _
  refine ZFSet.mem_sep.trans ⟨And.right, ?_⟩
  intro h
  obtain ⟨value, evaluates⟩ := h
  exact ⟨rankSteelEvaluates_input k alpha evaluates, value, evaluates⟩

theorem rankSteelEvaluation_value_exists {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda)
    (input : (rankSteelEvaluationDomain hl k alpha).val) :
    ∃ value : (rankSteelHull hl k alpha).val, RankSteelEvaluates k alpha input.val value.val := by
  obtain ⟨value, evaluates⟩ := (rankSteelEvaluationDomain_mem hl k alpha input.val).mp input.property
  exact ⟨⟨value, rankSteelEvaluates_value hl k alpha evaluates⟩, evaluates⟩

noncomputable def rankSteelEvaluationFunction {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    (rankSteelEvaluationDomain hl k alpha).val → (rankSteelHull hl k alpha).val :=
  fun input => Classical.choose (rankSteelEvaluation_value_exists hl k alpha input)

theorem rankSteelEvaluationFunction_spec {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda)
    (input : (rankSteelEvaluationDomain hl k alpha).val) :
    RankSteelEvaluates k alpha input.val (rankSteelEvaluationFunction hl k alpha input).val :=
  Classical.choose_spec (rankSteelEvaluation_value_exists hl k alpha input)

noncomputable def rankSteelEvaluationGraph {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) : RankDomain lambda :=
  rankFunctionGraph hl (rankSteelEvaluationDomain hl k alpha) (rankSteelHull hl k alpha)
    (rankSteelEvaluationFunction hl k alpha)

theorem rankSteelEvaluationGraph_isFunction {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    rankIsFunction (rankSteelEvaluationGraph hl k alpha) (rankSteelEvaluationDomain hl k alpha)
      (rankSteelHull hl k alpha) := rankFunctionGraph_isFunction hl _ _ _

theorem rankSteelEvaluationGraph_applies_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) (input value : RankDomain lambda) :
    rankGraphApplies (rankSteelEvaluationGraph hl k alpha) input value ↔
      RankSteelEvaluates k alpha input.val value.val := by
  rw [rankGraphApplies_iff hl]
  change ZFSet.pair input.val value.val ∈ zfFunctionGraph (rankSteelEvaluationFunction hl k alpha) ↔ _
  rw [mem_zfFunctionGraph]
  constructor
  · rintro ⟨member, same⟩
    have evaluates := rankSteelEvaluationFunction_spec hl k alpha ⟨input.val, member⟩
    rwa [same] at evaluates
  · intro evaluates
    have member := (rankSteelEvaluationDomain_mem hl k alpha input.val).mpr ⟨value.val, evaluates⟩
    exact ⟨member, rankSteelEvaluates_unique hl k alpha
      (rankSteelEvaluationFunction_spec hl k alpha ⟨input.val, member⟩) evaluates⟩

theorem rankSteelEvaluationFunction_surjective {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    Function.Surjective (rankSteelEvaluationFunction hl k alpha) := by
  intro value
  obtain ⟨f, s, hf, hs, function, edge⟩ := (rankSteelHull_mem hl k alpha value.val).mp value.property
  have evaluates : RankSteelEvaluates k alpha (ZFSet.pair f.val s.val) value.val :=
    ⟨f, s, hf, hs, function, rfl, edge⟩
  let input : (rankSteelEvaluationDomain hl k alpha).val := ⟨ZFSet.pair f.val s.val,
    (rankSteelEvaluationDomain_mem hl k alpha _).mpr ⟨value.val, evaluates⟩⟩
  exact ⟨input, Subtype.ext (rankSteelEvaluates_unique hl k alpha
    (rankSteelEvaluationFunction_spec hl k alpha input) evaluates)⟩

theorem rankSteelHull_card_le_domain {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    (rankSteelHull hl k alpha).val.card ≤ (rankSteelEvaluationDomain hl k alpha).val.card := by
  have bound := Cardinal.mk_le_of_surjective (rankSteelEvaluationFunction_surjective hl k alpha)
  simpa only [ZFSet.cardinalMk_coe_sort, Cardinal.lift_le] using bound

theorem rankSteelEvaluationDomain_rank_lt {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha gamma : OrdinalDomain lambda)
    (limit : Order.IsSuccLimit gamma.val) (below : alpha < gamma) :
    (rankSteelEvaluationDomain hl k alpha).val.rank < gamma.val := by
  change (ZFSet.sep (fun p => ∃ value, RankSteelEvaluates k alpha p value)
    (ZFSet.prod (rankHierarchy alpha).val (rankHierarchy alpha).val)).rank < _
  apply rank_graph_lt_of_limit limit (x := (rankHierarchy alpha).val) (y := (rankHierarchy alpha).val)
  · simpa only [rankHierarchy, ZFSet.rank_vonNeumann] using below
  · simpa only [rankHierarchy, ZFSet.rank_vonNeumann] using below
  · exact fun _ h => (ZFSet.mem_sep.mp h).1

/-- Steel's small-range bound is obtained from the actual partial evaluation
domain and a true critical point at gamma. -/
theorem rankSteelHull_card_lt_critical {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda)
    {owner : RankElementaryEmbedding lambda} {gamma : OrdinalDomain lambda}
    (cp : RankCriticalPoint owner gamma) (below : alpha < gamma) :
    (rankSteelHull hl k alpha).val.card < gamma.val.card :=
  (rankSteelHull_card_le_domain hl k alpha).trans_lt
    (rankCriticalPoint_low_rank_card_lt hl cp (rankSteelEvaluationDomain_rank_lt hl k alpha gamma
      (rankCriticalPoint_isSuccLimit hl cp) below))

end FullMarkedBLP
