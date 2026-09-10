import FullMarkedBLP.RankRestrictionGraph

namespace FullMarkedBLP
open FirstOrder Language

theorem rankGraphAppliesFormula_realize_valuation {lambda : Ordinal.{u}}
    (v : Fin 3 → RankDomain lambda) :
    rankGraphAppliesFormula.Realize v ↔ rankGraphApplies (v 0) (v 1) (v 2) := by
  have same : v = ![v 0, v 1, v 2] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  conv_lhs => rw [same]
  exact rankGraphAppliesFormula_realize _ _ _

def RankGraphPreserves {lambda : Ordinal.{u}} {n : Nat}
    (phi : membershipLanguage.Formula (Fin n)) (graph : RankDomain lambda) : Prop :=
  ∀ xs ys : Fin n → RankDomain lambda, (∀ i, rankGraphApplies graph (xs i) (ys i)) →
    (phi.Realize ys ↔ phi.Realize xs)

/-- For each particular formula, preservation on a set graph is itself a
first-order statement. This avoids assuming a satisfaction predicate. -/
noncomputable def rankGraphPreservesFormula {n : Nat}
    (phi : membershipLanguage.Formula (Fin n)) : membershipLanguage.Formula (Fin 1) :=
  Formula.iAlls (Fin n ⊕ Fin n)
    ((Formula.iInf fun i : Fin n => rankGraphAppliesFormula.relabel
      ![Sum.inl 0, Sum.inr (Sum.inl i), Sum.inr (Sum.inr i)]).imp
      ((phi.relabel (fun i => Sum.inr (Sum.inr i))).iff
        (phi.relabel (fun i => Sum.inr (Sum.inl i)))))

theorem rankGraphPreservesFormula_realize {lambda : Ordinal.{u}} {n : Nat}
    (phi : membershipLanguage.Formula (Fin n)) (graph : RankDomain lambda) :
    (rankGraphPreservesFormula phi).Realize ![graph] ↔ RankGraphPreserves phi graph := by
  simp only [rankGraphPreservesFormula, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iInf, Formula.realize_relabel, Formula.realize_iff,
    rankGraphAppliesFormula_realize_valuation, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  constructor
  · intro h xs ys applies
    exact h (Sum.elim xs ys) applies
  · intro h v applies
    exact h (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) applies

theorem rankElementary_graphPreserves_iff {lambda : Ordinal.{u}} {n : Nat}
    (j : RankElementaryEmbedding lambda) (phi : membershipLanguage.Formula (Fin n))
    (graph : RankDomain lambda) : RankGraphPreserves phi (j graph) ↔ RankGraphPreserves phi graph := by
  have result := j.map_formula (rankGraphPreservesFormula phi) ![graph]
  have same : j ∘ ![graph] = ![j graph] := by
    funext i
    have eq : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [same, rankGraphPreservesFormula_realize, rankGraphPreservesFormula_realize] at result
  exact result

theorem rankRestrictionGraph_preserves_formula {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (k : RankElementaryEmbedding lambda) (domain : RankDomain lambda) {n : Nat}
    (phi : membershipLanguage.Formula (Fin n)) : RankGraphPreserves phi (rankRestrictionGraph hl k domain) := by
  intro xs ys applies
  have same : ys = k ∘ xs := by
    funext i
    exact ((rankRestrictionGraph_applies_iff hl k domain (xs i) (ys i)).mp (applies i)).2.symm
  rw [same]
  exact k.map_formula phi xs

theorem rankRestrictionGraph_image_preserves_formula {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda) (domain : RankDomain lambda) {n : Nat}
    (phi : membershipLanguage.Formula (Fin n)) : RankGraphPreserves phi (j (rankRestrictionGraph hl k domain)) :=
  (rankElementary_graphPreserves_iff j phi _).mpr (rankRestrictionGraph_preserves_formula hl k domain phi)

end FullMarkedBLP
