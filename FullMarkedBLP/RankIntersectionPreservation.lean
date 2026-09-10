import FullMarkedBLP.RankSubsetPreservation

namespace FullMarkedBLP
open FirstOrder Language

noncomputable def rankIntersection {lambda : Ordinal.{u}} (x y : RankDomain lambda) : RankDomain lambda :=
  ⟨x.val ∩ y.val, (ZFSet.rank_mono (fun _ hw => (ZFSet.mem_inter.mp hw).1)).trans_lt x.property⟩

def rankIntersectionFormula : membershipLanguage.Formula (Fin 3) :=
  .all ((rankMemAt (.inr 0) (.inl 0)).iff
    ((rankMemAt (.inr 0) (.inl 1)) ⊓ (rankMemAt (.inr 0) (.inl 2))))

theorem rankIntersectionFormula_realize {lambda : Ordinal.{u}} (result x y : RankDomain lambda) :
    rankIntersectionFormula.Realize ![result, x, y] ↔ result.val = x.val ∩ y.val := by
  have semantics : rankIntersectionFormula.Realize ![result, x, y] ↔
      ∀ z : RankDomain lambda, z.val ∈ result.val ↔ z.val ∈ x.val ∧ z.val ∈ y.val := by
    simp [rankIntersectionFormula, Formula.Realize, BoundedFormula.realize_all,
      BoundedFormula.realize_iff, BoundedFormula.realize_inf, rankMemAt_realize, Fin.snoc]
  rw [semantics]
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_inter]
    constructor
    · intro hz
      exact (h (rankMember result z hz)).mp hz
    · intro hz
      exact (h (rankMember x z hz.1)).mpr hz
  · intro same z
    rw [same, ZFSet.mem_inter]

theorem rankElementary_intersection {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    (x y : RankDomain lambda) : j (rankIntersection x y) = rankIntersection (j x) (j y) := by
  have result := j.map_formula rankIntersectionFormula ![rankIntersection x y, x, y]
  have same : j ∘ ![rankIntersection x y, x, y] = ![j (rankIntersection x y), j x, j y] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  rw [same, rankIntersectionFormula_realize, rankIntersectionFormula_realize] at result
  exact Subtype.ext (result.mpr rfl)

end FullMarkedBLP
