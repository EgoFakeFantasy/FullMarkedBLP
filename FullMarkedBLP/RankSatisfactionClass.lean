import FullMarkedBLP.RankSyntaxData
import FullMarkedBLP.RankFiniteAssignment

namespace FullMarkedBLP

def rankTruthHolds {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda) (truth : RankClass lambda)
    (code assignment : RankDomain lambda) : Prop := truth (rankOrderedPair hl code assignment)

def rankFormulaTruth {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda) (truth : RankClass lambda)
    {n : Nat} (phi : RankPredicateFormula 0 n) (values : Fin n → RankDomain lambda) : Prop :=
  rankTruthHolds hl truth (rankNat hl (rankSyntaxCode ⟨n, phi⟩)) (rankAssignment hl values)

/-- The actual satisfaction class, built from finite syntax and actual
assignment graphs. This is a class definition, not a truth axiom. -/
def rankSatisfaction {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda) : RankClass lambda :=
  fun pair => ∃ (n : Nat) (phi : RankPredicateFormula 0 n) (values : Fin n → RankDomain lambda),
    pair = rankOrderedPair hl (rankNat hl (rankSyntaxCode ⟨n, phi⟩)) (rankAssignment hl values) ∧
      phi.Realize Fin.elim0 values

theorem rankSatisfaction_realize {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {n : Nat} (phi : RankPredicateFormula 0 n) (values : Fin n → RankDomain lambda) :
    rankFormulaTruth hl (rankSatisfaction hl) phi values ↔ phi.Realize Fin.elim0 values := by
  constructor
  · rintro ⟨m, psi, other, same, truth⟩
    have parts := (rankOrderedPair_inj hl _ _ _ _).mp same
    have codes : rankSyntaxCode ⟨n, phi⟩ = rankSyntaxCode ⟨m, psi⟩ :=
      Nat.cast_injective (Ordinal.toZFSet_injective (congrArg Subtype.val parts.1))
    have formulas := rankSyntaxCode_injective codes
    have arity : n = m := (Sigma.mk.inj formulas).1
    subst m
    have formula : phi = psi := eq_of_heq (Sigma.mk.inj formulas).2
    subst psi
    have assignment := rankAssignment_injective hl parts.2
    rwa [← assignment] at truth
  · exact fun truth => ⟨n, phi, values, rfl, truth⟩

/-- Semantic recursion clauses on correctly encoded formulas and
assignments. Their single finite-formula presentation is a separate theorem. -/
structure RankTruthConditions {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (truth : RankClass lambda) : Prop where
  falsum : ∀ (n : Nat) (v : Fin n → RankDomain lambda), ¬ rankFormulaTruth hl truth .falsum v
  equal : ∀ (n : Nat) (x y : Fin n) (v : Fin n → RankDomain lambda),
    rankFormulaTruth hl truth (.equal x y) v ↔ v x = v y
  member : ∀ (n : Nat) (x y : Fin n) (v : Fin n → RankDomain lambda),
    rankFormulaTruth hl truth (.member x y) v ↔ (v x).val ∈ (v y).val
  imp : ∀ (n : Nat) (p q : RankPredicateFormula 0 n) (v : Fin n → RankDomain lambda),
    rankFormulaTruth hl truth (.imp p q) v ↔ (rankFormulaTruth hl truth p v → rankFormulaTruth hl truth q v)
  all : ∀ (n : Nat) (p : RankPredicateFormula 0 (n + 1)) (v : Fin n → RankDomain lambda),
    rankFormulaTruth hl truth (.all p) v ↔ ∀ x : RankDomain lambda,
      rankFormulaTruth hl truth p (Fin.snoc v x)

theorem rankSatisfaction_conditions {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda) :
    RankTruthConditions hl (rankSatisfaction hl) := by
  constructor
  · intro n v
    rw [rankSatisfaction_realize]
    exact id
  · intro n x y v
    exact rankSatisfaction_realize hl _ _
  · intro n x y v
    exact rankSatisfaction_realize hl _ _
  · intro n p q v
    simp only [rankSatisfaction_realize, RankPredicateFormula.Realize]
  · intro n p v
    simp only [rankSatisfaction_realize, RankPredicateFormula.Realize]

/-- Any class satisfying the recursion clauses agrees with actual truth
on all valid formula/assignment pairs, by structural induction. -/
theorem RankTruthConditions.realize {lambda : Ordinal.{u}} {hl : Order.IsSuccLimit lambda}
    {truth : RankClass lambda} (conditions : RankTruthConditions hl truth)
    {n : Nat} (phi : RankPredicateFormula 0 n) (values : Fin n → RankDomain lambda) :
    rankFormulaTruth hl truth phi values ↔ phi.Realize Fin.elim0 values := by
  induction phi with
  | falsum => exact iff_false_intro (conditions.falsum _ values)
  | equal x y => exact conditions.equal _ x y values
  | member x y => exact conditions.member _ x y values
  | predicate a _ => exact Fin.elim0 a
  | imp p q ihp ihq => exact (conditions.imp _ p q values).trans (imp_congr (ihp values) (ihq values))
  | all p ih => exact (conditions.all _ p values).trans (forall_congr' (fun x => ih (Fin.snoc values x)))

end FullMarkedBLP
