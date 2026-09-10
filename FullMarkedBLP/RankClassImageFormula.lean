import FullMarkedBLP.RankElementaryDefinability

namespace FullMarkedBLP

def rankClassRestricted {lambda : Ordinal.{u}} (inner : RankClass lambda)
    (domain restricted : RankDomain lambda) : Prop :=
  ∀ z : RankDomain lambda, z.val ∈ restricted.val ↔ z.val ∈ domain.val ∧ inner z

def rankFormulaClassRestriction {m n : Nat} (inner : Fin m) (domain restricted : Fin n) :
    RankPredicateFormula m n :=
  .all ((RankPredicateFormula.member (Fin.last n) restricted.castSucc).iff
    ((RankPredicateFormula.member (Fin.last n) domain.castSucc).and (.predicate inner (Fin.last n))))

theorem rankFormulaClassRestriction_realize {lambda : Ordinal.{u}} {m n : Nat}
    (inner : Fin m) (domain restricted : Fin n) (classes : Fin m → RankClass lambda)
    (values : Fin n → RankDomain lambda) :
    (rankFormulaClassRestriction inner domain restricted).Realize classes values ↔
      values restricted = rankClassRestriction (classes inner) (values domain) := by
  simp only [rankFormulaClassRestriction, RankPredicateFormula.Realize,
    RankPredicateFormula.realize_iff, RankPredicateFormula.realize_and,
    Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · intro h
    apply Subtype.ext
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact (rankClassRestriction_mem _ _ (rankMember (values restricted) z hz)).mpr
        ((h (rankMember (values restricted) z hz)).mp hz)
    · intro hz
      exact (h (rankMember (rankClassRestriction (classes inner) (values domain)) z hz)).mpr
        ((rankClassRestriction_mem _ _ _).mp hz)
  · intro same z
    rw [same]
    exact rankClassRestriction_mem _ _ z

theorem rankFormulaClassRestriction_realize_raw {lambda : Ordinal.{u}} {m n : Nat}
    (inner : Fin m) (domain restricted : Fin n) (classes : Fin m → RankClass lambda)
    (values : Fin n → RankDomain lambda) :
    (rankFormulaClassRestriction inner domain restricted).Realize classes values ↔
      rankClassRestricted (classes inner) (values domain) (values restricted) := by
  simp only [rankFormulaClassRestriction, RankPredicateFormula.Realize,
    RankPredicateFormula.realize_iff, RankPredicateFormula.realize_and,
    Fin.snoc_last, Fin.snoc_castSucc, rankClassRestricted]

theorem rankClassRestricted_iff {lambda : Ordinal.{u}} (inner : RankClass lambda)
    (domain restricted : RankDomain lambda) :
    rankClassRestricted inner domain restricted ↔ restricted = rankClassRestriction inner domain :=
  (rankFormulaClassRestriction_realize_raw (0 : Fin 1) (0 : Fin 2) 1
    (fun _ => inner) ![domain, restricted]).symm.trans
      (rankFormulaClassRestriction_realize 0 0 1 (fun _ : Fin 1 => inner) ![domain, restricted])

/-- The entire class-image equation, using actual bounded restrictions.
Class variables are outer embedding graph, inner class, and resulting class. -/
def rankClassImageMatrix : RankPredicateFormula 3 0 :=
  let imageBody : RankPredicateFormula 3 4 :=
    (rankFormulaClassRestriction 1 1 2).and
      ((rankFormulaTruthHolds 0 2 3).and (.member 0 3))
  let body : RankPredicateFormula 3 1 := (RankPredicateFormula.predicate 2 0).iff imageBody.ex.ex.ex
  body.all

theorem rankClassImageMatrix_realize {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (inner result : RankClass lambda) :
    rankClassImageMatrix.Realize ![rankEmbeddingClassGraph j, inner, result] Fin.elim0 ↔
      result = rankClassImage j inner := by
  have graphQuery (x y : RankDomain lambda) :
      rankTruthHolds hl (rankEmbeddingClassGraph j) x y ↔ j x = y :=
    rankEmbeddingClassGraph_pair hl j x y
  have raw (outer : RankClass lambda) : rankClassImageMatrix.Realize ![outer, inner, result] Fin.elim0 ↔
      ∀ x : RankDomain lambda, result x ↔ ∃ domain restricted image : RankDomain lambda,
        rankClassRestricted inner domain restricted ∧ rankTruthHolds hl outer restricted image ∧ x.val ∈ image.val := by
    simp only [rankClassImageMatrix, RankPredicateFormula.Realize, RankPredicateFormula.realize_iff,
      RankPredicateFormula.realize_ex, RankPredicateFormula.realize_and,
      rankFormulaClassRestriction_realize_raw, rankFormulaTruthHolds_realize hl]
    rfl
  have semantics := raw (rankEmbeddingClassGraph j)
  simp only [graphQuery, rankClassRestricted_iff] at semantics
  rw [semantics]
  constructor
  · intro h
    ext x
    change result x ↔ rankClassImage j inner x
    rw [h]
    constructor
    · rintro ⟨domain, restricted, image, restrictionEq, imageEq, member⟩
      refine ⟨domain, ?_⟩
      rw [← restrictionEq, imageEq]
      exact member
    · rintro ⟨domain, member⟩
      exact ⟨domain, _, _, rfl, rfl, member⟩
  · rintro rfl x
    constructor
    · rintro ⟨domain, member⟩
      exact ⟨domain, _, _, rfl, rfl, member⟩
    · rintro ⟨domain, restricted, image, restrictionEq, imageEq, member⟩
      refine ⟨domain, ?_⟩
      rw [← restrictionEq, imageEq]
      exact member

def rankFormulaClassImage {m n : Nat} (outer inner result : Fin m) : RankPredicateFormula m n :=
  (rankClassImageMatrix.relabelClasses ![outer, inner, result]).relabelSets Fin.elim0

theorem rankFormulaClassImage_realize {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {m n : Nat} (outer inner result : Fin m) (classes : Fin m → RankClass lambda)
    (values : Fin n → RankDomain lambda) (j : RankElementaryEmbedding lambda)
    (outerGraph : classes outer = rankEmbeddingClassGraph j) :
    (rankFormulaClassImage (n := n) outer inner result).Realize classes values ↔
      classes result = rankClassImage j (classes inner) := by
  rw [rankFormulaClassImage, RankPredicateFormula.realize_relabelSets,
    RankPredicateFormula.realize_relabelClasses, rankMapTriple, outerGraph]
  have empty : values ∘ (Fin.elim0 : Fin 0 → Fin n) = Fin.elim0 := Subsingleton.elim _ _
  rw [empty]
  exact rankClassImageMatrix_realize hl j _ _

end FullMarkedBLP
