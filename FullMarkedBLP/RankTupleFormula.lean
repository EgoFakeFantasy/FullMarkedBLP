import FullMarkedBLP.RankTruthFormulaAtoms

namespace FullMarkedBLP

namespace RankPredicateFormula

def or {m n : Nat} (p q : RankPredicateFormula m n) : RankPredicateFormula m n :=
  imp p.not q

def iff {m n : Nat} (p q : RankPredicateFormula m n) : RankPredicateFormula m n :=
  (imp p q).and (imp q p)

theorem realize_or {lambda : Ordinal.{u}} {m n : Nat} (p q : RankPredicateFormula m n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda) :
    (p.or q).Realize classes values ↔ p.Realize classes values ∨ q.Realize classes values := by
  classical
  by_cases h : p.Realize classes values <;> simp [or, not, Realize, h]

theorem realize_iff {lambda : Ordinal.{u}} {m n : Nat} (p q : RankPredicateFormula m n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda) :
    (p.iff q).Realize classes values ↔ (p.Realize classes values ↔ q.Realize classes values) := by
  rw [iff, realize_and]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

end RankPredicateFormula

def rankFormulaEmpty {m n : Nat} (x : Fin n) : RankPredicateFormula m n :=
  rankPredicateAtom rankEmptyFormula ![x]

theorem rankFormulaEmpty_realize {lambda : Ordinal.{u}} {m n : Nat} (x : Fin n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda) :
    (rankFormulaEmpty x).Realize classes values ↔ (values x).val = ∅ := by
  rw [rankFormulaEmpty, rankPredicateAtom_realize]
  have mapped : values ∘ ![x] = ![values x] := by
    funext i
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    rfl
  rw [mapped]
  exact rankEmptyFormula_realize _

noncomputable def rankTuple {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda) :
    {k : Nat} → (Fin k → RankDomain lambda) → RankDomain lambda
  | 0, _ => ⟨∅, by simpa only [ZFSet.rank_empty] using hl.pos⟩
  | k + 1, values => rankOrderedPair hl (values 0) (rankTuple hl (fun i : Fin k => values i.succ))

theorem rankTuple_injective {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda) {k : Nat} :
    Function.Injective (@rankTuple lambda hl k) := by
  intro values other same
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    have pair := ZFSet.pair_inj.mp (congrArg Subtype.val same)
    have head : values 0 = other 0 := Subtype.ext pair.1
    have tail := ih (Subtype.ext pair.2)
    funext i
    exact Fin.cases head (fun i => congrFun tail i) i

theorem rankTuple_nat {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda) {k : Nat}
    (values : Fin k → Nat) :
    (rankTuple hl (rankNat hl ∘ values)).val = zfNatTuple values := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ZFSet.pair _ (rankTuple hl (rankNat hl ∘ (fun i : Fin k => values i.succ))).val = _
    rw [ih]
    rfl

/-- The tuple length is a metalevel natural, so each instance is one finite
first-order formula. Its entries can be arbitrary sets in the rank domain. -/
def rankFormulaTuple {m : Nat} : {k n : Nat} → Fin n → (Fin k → Fin n) → RankPredicateFormula m n
  | 0, _, tuple, _ => rankFormulaEmpty tuple
  | k + 1, n, tuple, entries =>
    ((rankFormulaOrderedPair tuple.castSucc (entries 0).castSucc (Fin.last n)).and
      (rankFormulaTuple (Fin.last n) (fun i : Fin k => (entries i.succ).castSucc))).ex

theorem rankFormulaTuple_realize {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {m k n : Nat} (tuple : Fin n) (entries : Fin k → Fin n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda) :
    (rankFormulaTuple tuple entries).Realize classes values ↔
      values tuple = rankTuple hl (values ∘ entries) := by
  induction k generalizing n with
  | zero =>
    rw [rankFormulaTuple, rankFormulaEmpty_realize]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  | succ k ih =>
    simp only [rankFormulaTuple, RankPredicateFormula.realize_ex,
      RankPredicateFormula.realize_and, rankFormulaOrderedPair_realize, ih,
      Function.comp_def, Fin.snoc_castSucc, Fin.snoc_last]
    constructor
    · rintro ⟨tail, ordered, same⟩
      subst tail
      exact Subtype.ext ((rankIsOrderedPair_iff hl _ _ _).mp ordered)
    · intro same
      refine ⟨rankTuple hl (fun i : Fin k => values (entries i.succ)), ?_, rfl⟩
      apply (rankIsOrderedPair_iff hl _ _ _).mpr
      exact congrArg Subtype.val same

def rankFormulaTupleMem {m n k : Nat} (book : Fin n) (entries : Fin k → Fin n) :
    RankPredicateFormula m n :=
  ((RankPredicateFormula.member (Fin.last n) book.castSucc).and
    (rankFormulaTuple (Fin.last n) (fun i => (entries i).castSucc))).ex

theorem rankFormulaTupleMem_realize {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {m n k : Nat} (book : Fin n) (entries : Fin k → Fin n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda) :
    (rankFormulaTupleMem book entries).Realize classes values ↔
      (rankTuple hl (values ∘ entries)).val ∈ (values book).val := by
  simp only [rankFormulaTupleMem, RankPredicateFormula.realize_ex,
    RankPredicateFormula.realize_and, RankPredicateFormula.Realize,
    rankFormulaTuple_realize hl, Function.comp_def, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨tuple, member, rfl⟩
    exact member
  · exact fun member => ⟨_, member, rfl⟩

/-- Reading an actual natural table cannot produce spurious nonnatural
coordinates; all coordinates are recovered from its actual tuple range. -/
theorem rankTuple_mem_natRelation {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) {k : Nat} (relation : (Fin k → Nat) → Prop)
    (values : Fin k → RankDomain lambda) :
    (rankTuple hl values).val ∈ (rankNatRelation hw relation).val ↔
      ∃ tuple : Fin k → Nat, relation tuple ∧ values = rankNat hl ∘ tuple := by
  change (rankTuple hl values).val ∈ zfNatRelation relation ↔ _
  rw [zfNatRelation, ZFSet.mem_range]
  constructor
  · rintro ⟨tuple, same⟩
    refine ⟨tuple.val, tuple.property, rankTuple_injective hl ?_⟩
    apply Subtype.ext
    rw [rankTuple_nat]
    exact same.symm
  · rintro ⟨tuple, member, rfl⟩
    exact ⟨⟨tuple, member⟩, (rankTuple_nat hl tuple).symm⟩

end FullMarkedBLP
