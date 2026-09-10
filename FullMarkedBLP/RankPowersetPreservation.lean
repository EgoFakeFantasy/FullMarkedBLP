import FullMarkedBLP.RankSubsetPreservation

namespace FullMarkedBLP
open FirstOrder Language

def rankPowersetFormula : membershipLanguage.Formula (Fin 2) :=
  .all ((rankMemAt (.inr 0) (.inl 0)).iff
    (.all ((rankMemAt (.inr 1) (.inr 0)).imp (rankMemAt (.inr 1) (.inl 1)))))

theorem rankPowersetFormula_realize {lambda : Ordinal.{u}} (p x : RankDomain lambda) :
    rankPowersetFormula.Realize ![p, x] ↔ p.val = ZFSet.powerset x.val := by
  have semantics : rankPowersetFormula.Realize ![p, x] ↔
      ∀ z : RankDomain lambda, z.val ∈ p.val ↔
        ∀ w : RankDomain lambda, w.val ∈ z.val → w.val ∈ x.val := by
    simp [rankPowersetFormula, Formula.Realize, BoundedFormula.realize_all,
      BoundedFormula.realize_iff, BoundedFormula.realize_imp, rankMemAt_realize, Fin.snoc]
  rw [semantics]
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_powerset]
    constructor
    · intro hz w hw
      let z' := rankMember p z hz
      exact (h z').mp hz (rankMember z' w hw) hw
    · intro hz
      let z' : RankDomain lambda := ⟨z, (ZFSet.rank_mono hz).trans_lt x.property⟩
      exact (h z').mpr (fun w hw => hz hw)
  · intro eq z
    rw [eq, ZFSet.mem_powerset]
    constructor
    · intro hz w hw
      exact hz hw
    · intro hz w hw
      exact hz (rankMember z w hw) hw

noncomputable def rankPowerset {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (x : RankDomain lambda) : RankDomain lambda :=
  ⟨ZFSet.powerset x.val, by rw [ZFSet.rank_powerset]; exact hl.succ_lt x.property⟩

theorem rankElementary_powerset {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (x : RankDomain lambda) :
    j (rankPowerset hl x) = rankPowerset hl (j x) := by
  have result := j.map_formula rankPowersetFormula ![rankPowerset hl x, x]
  have same : j ∘ ![rankPowerset hl x, x] = ![j (rankPowerset hl x), j x] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => omega
  rw [same, rankPowersetFormula_realize, rankPowersetFormula_realize] at result
  exact Subtype.ext (result.mpr rfl)

end FullMarkedBLP
