import FullMarkedBLP.RankElementarity

namespace FullMarkedBLP

/-- Every member of a rank-domain element belongs to the same domain. -/
def rankMember {lambda : Ordinal.{u}} (x : RankDomain lambda) (y : ZFSet.{u})
    (hy : y ∈ x.val) : RankDomain lambda :=
  ⟨y, (ZFSet.rank_lt_of_mem hy).trans x.property⟩

def rankIsOrdinal {lambda : Ordinal.{u}} (x : RankDomain lambda) : Prop :=
  (∀ y z : RankDomain lambda, y.val ∈ z.val → z.val ∈ x.val → y.val ∈ x.val) ∧
  (∀ y z w : RankDomain lambda, y.val ∈ z.val → z.val ∈ w.val →
    w.val ∈ x.val → y.val ∈ w.val)

theorem rankIsOrdinal_iff {lambda : Ordinal.{u}} (x : RankDomain lambda) :
    rankIsOrdinal x ↔ ZFSet.IsOrdinal x.val := by
  constructor
  · rintro ⟨htrans, hmem⟩
    constructor
    · intro y hy z hz
      let y' := rankMember x y hy
      let z' := rankMember y' z hz
      exact htrans z' y' hz hy
    · intro y z w hyz hzw hwx
      let w' := rankMember x w hwx
      let z' := rankMember w' z hzw
      let y' := rankMember z' y hyz
      exact hmem y' z' w' hyz hzw hwx
  · intro hx
    exact ⟨fun y z hyz hzx => hx.mem_trans hyz hzx,
      fun y z w hyz hzw hwx => hx.mem_trans' hyz hzw hwx⟩

open FirstOrder Language

def rankMemAtom {n : Nat} (i j : Fin 1 ⊕ Fin n) : membershipLanguage.BoundedFormula (Fin 1) n :=
  (show membershipLanguage.Relations 2 from ⟨rfl⟩).boundedFormula₂ (.var i) (.var j)

def rankTransitiveFormula : membershipLanguage.Formula (Fin 1) :=
  .all (.all ((rankMemAtom (.inr 0) (.inr 1)).imp
    ((rankMemAtom (.inr 1) (.inl 0)).imp (rankMemAtom (.inr 0) (.inl 0)))))

theorem rankTransitiveFormula_realize {lambda : Ordinal.{u}} (x : RankDomain lambda) :
    rankTransitiveFormula.Realize ![x] ↔
      ∀ y z : RankDomain lambda, y.val ∈ z.val → z.val ∈ x.val → y.val ∈ x.val := by
  simp [rankTransitiveFormula, rankMemAtom, Formula.Realize, BoundedFormula.Realize,
    FirstOrder.Language.Relations.boundedFormula₂, FirstOrder.Language.Relations.boundedFormula,
    Structure.RelMap, Fin.snoc]

def rankMemTransitiveFormula : membershipLanguage.Formula (Fin 1) :=
  .all (.all (.all ((rankMemAtom (.inr 0) (.inr 1)).imp
    ((rankMemAtom (.inr 1) (.inr 2)).imp
      ((rankMemAtom (.inr 2) (.inl 0)).imp (rankMemAtom (.inr 0) (.inr 2)))))))

theorem rankMemTransitiveFormula_realize {lambda : Ordinal.{u}} (x : RankDomain lambda) :
    rankMemTransitiveFormula.Realize ![x] ↔
      ∀ y z w : RankDomain lambda, y.val ∈ z.val → z.val ∈ w.val →
        w.val ∈ x.val → y.val ∈ w.val := by
  simp [rankMemTransitiveFormula, rankMemAtom, Formula.Realize, BoundedFormula.Realize,
    FirstOrder.Language.Relations.boundedFormula₂, FirstOrder.Language.Relations.boundedFormula,
    Structure.RelMap, Fin.snoc]

def rankOrdinalFormula : membershipLanguage.Formula (Fin 1) :=
  rankTransitiveFormula ⊓ rankMemTransitiveFormula

theorem rankOrdinalFormula_realize {lambda : Ordinal.{u}} (x : RankDomain lambda) :
    rankOrdinalFormula.Realize ![x] ↔ ZFSet.IsOrdinal x.val := by
  rw [← rankIsOrdinal_iff x]
  change (rankTransitiveFormula ⊓ rankMemTransitiveFormula).Realize ![x] ↔ _
  simp only [Formula.Realize, BoundedFormula.realize_inf]
  exact and_congr (rankTransitiveFormula_realize x) (rankMemTransitiveFormula_realize x)

theorem rankElementary_isOrdinal_iff {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (x : RankDomain lambda) :
    ZFSet.IsOrdinal (j x).val ↔ ZFSet.IsOrdinal x.val := by
  have h := j.map_formula rankOrdinalFormula ![x]
  have he : (j ∘ ![x]) = ![j x] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [he] at h
  exact (rankOrdinalFormula_realize (j x)).symm.trans (h.trans (rankOrdinalFormula_realize x))

end FullMarkedBLP


