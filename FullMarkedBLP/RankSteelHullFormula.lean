import FullMarkedBLP.RankSteelHull

namespace FullMarkedBLP
open FirstOrder Language

def rankOrdinalFunctionAt {alpha : Type} {n : Nat} (f : alpha ⊕ Fin n) :
    membershipLanguage.BoundedFormula alpha n :=
  BoundedFormula.relabel ![f] rankOrdinalFunctionFormula

theorem rankOrdinalFunctionAt_realize {lambda : Ordinal.{u}} {alpha : Type} {n : Nat}
    (f : alpha ⊕ Fin n) (v : alpha → RankDomain lambda) (xs : Fin n → RankDomain lambda) :
    (rankOrdinalFunctionAt f).Realize v xs ↔ RankOrdinalFunction (Sum.elim v xs f) := by
  simp only [rankOrdinalFunctionAt, BoundedFormula.realize_relabel]
  change rankOrdinalFunctionFormula.Realize (Sum.elim v xs ∘ ![f]) ↔ _
  have same : Sum.elim v xs ∘ ![f] = ![Sum.elim v xs f] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [same]
  exact rankOrdinalFunctionFormula_realize _

/-- A first-order description of the hull using the embedding's actual
restriction graph on the specified level. No external embedding symbol
occurs in this description. -/
def RankSteelHullDescribes {lambda : Ordinal.{u}} (hull level restriction : RankDomain lambda) : Prop :=
  ∀ z : RankDomain lambda, z.val ∈ hull.val ↔
    ∃ f s output : RankDomain lambda, f.val ∈ level.val ∧ s.val ∈ level.val ∧
      RankOrdinalFunction f ∧ rankGraphApplies restriction f output ∧ rankGraphApplies output s z

def rankSteelHullFormula : membershipLanguage.Formula (Fin 3) :=
  .all ((rankMemAt (.inr 0) (.inl 0)).iff
    (.ex (.ex (.ex ((rankMemAt (.inr 1) (.inl 1)) ⊓
      ((rankMemAt (.inr 2) (.inl 1)) ⊓ ((rankOrdinalFunctionAt (.inr 1)) ⊓
        ((rankGraphAppliesAt (.inl 2) (.inr 1) (.inr 3)) ⊓
          rankGraphAppliesAt (.inr 3) (.inr 2) (.inr 0)))))))))

theorem rankSteelHullFormula_realize {lambda : Ordinal.{u}} (hull level restriction : RankDomain lambda) :
    rankSteelHullFormula.Realize ![hull, level, restriction] ↔ RankSteelHullDescribes hull level restriction := by
  simp [rankSteelHullFormula, Formula.Realize, BoundedFormula.Realize, rankMemAt_realize,
    rankOrdinalFunctionAt_realize, rankGraphAppliesAt_realize, RankSteelHullDescribes, Fin.snoc]

theorem rankElementary_hullDescribes_iff {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (hull level restriction : RankDomain lambda) :
    RankSteelHullDescribes (j hull) (j level) (j restriction) ↔ RankSteelHullDescribes hull level restriction := by
  have result := j.map_formula rankSteelHullFormula ![hull, level, restriction]
  have same : j ∘ ![hull, level, restriction] = ![j hull, j level, j restriction] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  rw [same, rankSteelHullFormula_realize, rankSteelHullFormula_realize] at result
  exact result

theorem rankSteelHull_describes_of_restriction {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) (restriction : RankDomain lambda)
    (describes : ∀ f output : RankDomain lambda, rankGraphApplies restriction f output ↔
      f.val ∈ (rankHierarchy alpha).val ∧ k f = output) :
    RankSteelHullDescribes (rankSteelHull hl k alpha) (rankHierarchy alpha) restriction := by
  intro z
  rw [rankSteelHull_mem]
  constructor
  · rintro ⟨f, s, hf, hs, function, edge⟩
    have member := ZFSet.mem_vonNeumann.mpr hf
    exact ⟨f, s, k f, member, ZFSet.mem_vonNeumann.mpr hs, function,
      (describes f (k f)).mpr ⟨member, rfl⟩, (rankGraphApplies_iff hl _ _ _).mpr edge⟩
  · rintro ⟨f, s, output, hf, hs, function, restricted, edge⟩
    have same := ((describes f output).mp restricted).2
    refine ⟨f, s, ZFSet.mem_vonNeumann.mp hf, ZFSet.mem_vonNeumann.mp hs, function, ?_⟩
    rw [same]
    exact (rankGraphApplies_iff hl _ _ _).mp edge

theorem rankSteelHullDescribes_unique {lambda : Ordinal.{u}} {hull other level restriction : RankDomain lambda}
    (left : RankSteelHullDescribes hull level restriction)
    (right : RankSteelHullDescribes other level restriction) : hull = other := by
  have same : ∀ z : RankDomain lambda, z.val ∈ hull.val ↔ z.val ∈ other.val :=
    fun z => (left z).trans (right z).symm
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  exact ⟨fun hz => (same (rankMember hull z hz)).mp hz, fun hz => (same (rankMember other z hz)).mpr hz⟩

end FullMarkedBLP
