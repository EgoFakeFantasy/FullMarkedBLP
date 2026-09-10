import FullMarkedBLP.RankClassImage

namespace FullMarkedBLP
universe u

/-- Finitary first-order membership syntax with finitely many unary class
predicates. Quantifiers here range over sets in V_lambda, not over classes. -/
inductive RankPredicateFormula (classes : Nat) : Nat → Type
  | falsum {n} : RankPredicateFormula classes n
  | equal {n} (x y : Fin n) : RankPredicateFormula classes n
  | member {n} (x y : Fin n) : RankPredicateFormula classes n
  | predicate {n} (a : Fin classes) (x : Fin n) : RankPredicateFormula classes n
  | imp {n} (p q : RankPredicateFormula classes n) : RankPredicateFormula classes n
  | all {n} (p : RankPredicateFormula classes (n + 1)) : RankPredicateFormula classes n

namespace RankPredicateFormula

def Realize {lambda : Ordinal.{u}} {m n : Nat} : RankPredicateFormula m n →
    (Fin m → RankClass lambda) → (Fin n → RankDomain lambda) → Prop
  | .falsum, _, _ => False
  | .equal x y, _, v => v x = v y
  | .member x y, _, v => (v x).val ∈ (v y).val
  | .predicate a x, c, v => c a (v x)
  | .imp p q, c, v => p.Realize c v → q.Realize c v
  | .all p, c, v => ∀ x : RankDomain lambda, p.Realize c (Fin.snoc v x)

def not {m n : Nat} (p : RankPredicateFormula m n) : RankPredicateFormula m n := .imp p .falsum

def and {m n : Nat} (p q : RankPredicateFormula m n) : RankPredicateFormula m n :=
  (imp p q.not).not

def ex {m n : Nat} (p : RankPredicateFormula m (n + 1)) : RankPredicateFormula m n :=
  (all p.not).not

theorem realize_not {lambda : Ordinal.{u}} {m n : Nat} (p : RankPredicateFormula m n)
    (c : Fin m → RankClass lambda) (v : Fin n → RankDomain lambda) :
    p.not.Realize c v ↔ ¬ p.Realize c v := Iff.rfl

theorem realize_and {lambda : Ordinal.{u}} {m n : Nat} (p q : RankPredicateFormula m n)
    (c : Fin m → RankClass lambda) (v : Fin n → RankDomain lambda) :
    (p.and q).Realize c v ↔ p.Realize c v ∧ q.Realize c v := by
  classical
  simp [and, not, Realize]

theorem realize_ex {lambda : Ordinal.{u}} {m n : Nat} (p : RankPredicateFormula m (n + 1))
    (c : Fin m → RankClass lambda) (v : Fin n → RankDomain lambda) :
    p.ex.Realize c v ↔ ∃ x : RankDomain lambda, p.Realize c (Fin.snoc v x) := by
  classical
  simp [ex, not, Realize]

def relabelClasses {m n t : Nat} (f : Fin m → Fin t) : RankPredicateFormula m n → RankPredicateFormula t n
  | .falsum => .falsum
  | .equal x y => .equal x y
  | .member x y => .member x y
  | .predicate a x => .predicate (f a) x
  | .imp p q => .imp (p.relabelClasses f) (q.relabelClasses f)
  | .all p => .all (p.relabelClasses f)

theorem realize_relabelClasses {lambda : Ordinal.{u}} {m n t : Nat}
    (f : Fin m → Fin t) (p : RankPredicateFormula m n)
    (c : Fin t → RankClass lambda) (v : Fin n → RankDomain lambda) :
    (p.relabelClasses f).Realize c v ↔ p.Realize (c ∘ f) v := by
  induction p with
  | falsum => rfl
  | equal => rfl
  | member => rfl
  | predicate => rfl
  | imp p q ihp ihq => exact imp_congr (ihp v) (ihq v)
  | all p ih => exact forall_congr' (fun x => ih (Fin.snoc v x))

end RankPredicateFormula

/-- A finite existential block of class variables followed by an arbitrary
first-order matrix. Classes range over the entire powerset of V_lambda. -/
def rankSigmaOneSatisfies {lambda : Ordinal.{u}} {m n p : Nat}
    (matrix : RankPredicateFormula (m + p) n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda) : Prop :=
  ∃ witnesses : Fin p → RankClass lambda, matrix.Realize (Fin.append classes witnesses) values

def rankSigmaTwoSatisfies {lambda : Ordinal.{u}} {m n p q : Nat}
    (matrix : RankPredicateFormula ((m + p) + q) n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda) : Prop :=
  ∃ witnesses : Fin p → RankClass lambda, ∀ universals : Fin q → RankClass lambda,
    matrix.Realize (Fin.append (Fin.append classes witnesses) universals) values

/-- Standard Sigma-one second-order elementarity, with actual j-plus on
all class parameters and the original embedding on set parameters. -/
def RankSigmaOneElementary {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda) : Prop :=
  ∀ (m n p : Nat) (matrix : RankPredicateFormula (m + p) n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda),
    rankSigmaOneSatisfies matrix (rankClassImage j ∘ classes) (j ∘ values) ↔
      rankSigmaOneSatisfies matrix classes values

def RankSigmaTwoElementary {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda) : Prop :=
  ∀ (m n p q : Nat) (matrix : RankPredicateFormula ((m + p) + q) n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda),
    rankSigmaTwoSatisfies matrix (rankClassImage j ∘ classes) (j ∘ values) ↔
      rankSigmaTwoSatisfies matrix classes values

theorem rankClassAppendEmpty {lambda : Ordinal.{u}} {m : Nat}
    (classes : Fin m → RankClass lambda) (empty : Fin 0 → RankClass lambda) :
    Fin.append classes empty = classes := by
  funext i
  exact Fin.append_left classes empty i

theorem rankSigmaTwoSatisfies_zero {lambda : Ordinal.{u}} {m n p : Nat}
    (matrix : RankPredicateFormula (m + p) n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda) :
    rankSigmaTwoSatisfies (q := 0) matrix classes values ↔ rankSigmaOneSatisfies matrix classes values := by
  unfold rankSigmaTwoSatisfies rankSigmaOneSatisfies
  apply exists_congr
  intro witnesses
  constructor
  · intro h
    simpa only [rankClassAppendEmpty] using h Fin.elim0
  · intro h empty
    simpa only [rankClassAppendEmpty] using h

theorem rankSigmaTwoElementary_sigmaOne {lambda : Ordinal.{u}} {j : RankElementaryEmbedding lambda}
    (elementary : RankSigmaTwoElementary j) : RankSigmaOneElementary j := by
  intro m n p matrix classes values
  simpa only [rankSigmaTwoSatisfies_zero] using elementary m n p 0 matrix classes values

/-- The standard Sigma-two rank-embedding formulation of I2 used in the
source manuscript. This definition contains no BLP realization, linedness,
root extraction, or well-foundedness conclusion. -/
def RankI2 : Prop :=
  ∃ (lambda : Ordinal.{u}) (_hl : Order.IsSuccLimit lambda) (j : RankElementaryEmbedding lambda)
    (critical : OrdinalDomain lambda), RankCriticalPoint j critical ∧ RankSigmaTwoElementary j

end FullMarkedBLP
