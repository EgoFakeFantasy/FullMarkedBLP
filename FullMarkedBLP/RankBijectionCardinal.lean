import FullMarkedBLP.FunctionGraphConstruction

namespace FullMarkedBLP

def rankIsBijection {lambda : Ordinal.{u}} (f x y : RankDomain lambda) : Prop :=
  rankIsFunction f x y ∧ rankGraphOnto f x y ∧ rankGraphOneToOne f x

theorem rankBijection_card_eq {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {f x y : RankDomain lambda} (h : rankIsBijection f x y) : x.val.card = y.val.card := by
  exact zfGraph_card_eq ((rankIsFunction_iff hl f x y).mp h.1)
    ((rankGraphOnto_iff hl f x y).mp h.2.1)
    ((rankGraphOneToOne_iff hl f x y h.1.1).mp h.2.2)

theorem rankBijection_exists_iff_card_eq {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (x y : RankDomain lambda) :
    (∃ f : RankDomain lambda, rankIsBijection f x y) ↔ x.val.card = y.val.card := by
  constructor
  · rintro ⟨f, hf⟩
    exact rankBijection_card_eq hl hf
  · intro hc
    have hm : Cardinal.mk x.val = Cardinal.mk y.val := by
      rw [ZFSet.cardinalMk_coe_sort, ZFSet.cardinalMk_coe_sort, hc]
    obtain ⟨e⟩ := Cardinal.eq.mp hm
    let g := zfFunctionGraph e
    have hg := zfFunctionGraph_isFunc e
    let f : RankDomain lambda := ⟨g, rank_function_lt_of_limit hl x.property y.property hg⟩
    have hf : rankIsFunction f x y := (rankIsFunction_iff hl f x y).mpr hg
    refine ⟨f, hf, ?_, ?_⟩
    · exact (rankGraphOnto_iff hl f x y).mpr (zfFunctionGraph_onto e e.surjective)
    · exact (rankGraphOneToOne_iff hl f x y hf.1).mpr
        (zfFunctionGraph_oneToOne e e.injective)

end FullMarkedBLP

