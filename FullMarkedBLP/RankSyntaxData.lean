import FullMarkedBLP.RankPredicateTranslation
import FullMarkedBLP.RankCriticalInaccessible
import Mathlib.Tactic.DeriveCountable

namespace FullMarkedBLP

deriving instance Countable for RankPredicateFormula

abbrev RankPureSyntax := Sigma (RankPredicateFormula 0)

/-- Any injective natural-number encoding suffices: its entire constructor
table will be a fixed, low-rank parameter of the satisfaction formula. -/
noncomputable def rankSyntaxCode : RankPureSyntax → Nat :=
  Classical.choose (Countable.exists_injective_nat RankPureSyntax)

theorem rankSyntaxCode_injective : Function.Injective rankSyntaxCode :=
  Classical.choose_spec (Countable.exists_injective_nat RankPureSyntax)

noncomputable def zfNatTuple : {n : Nat} → (Fin n → Nat) → ZFSet.{u}
  | 0, _ => ∅
  | n + 1, values => ZFSet.pair (values 0 : Ordinal).toZFSet (zfNatTuple (fun i : Fin n => values i.succ))

theorem zfNatTuple_rank_lt {n : Nat} (values : Fin n → Nat) :
    (zfNatTuple.{u} values).rank < Ordinal.omega0 := by
  induction n with
  | zero => simpa only [zfNatTuple, ZFSet.rank_empty] using Ordinal.isSuccLimit_omega0.pos
  | succ n ih =>
    apply rank_orderedPair_lt_of_limit Ordinal.isSuccLimit_omega0
    · simpa only [Ordinal.rank_toZFSet] using Ordinal.natCast_lt_omega0 (values 0)
    · exact ih _

theorem zfNatTuple_injective {n : Nat} : Function.Injective (@zfNatTuple.{u} n) := by
  intro values other same
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    have pair := ZFSet.pair_inj.mp same
    have head : values 0 = other 0 := Nat.cast_injective (Ordinal.toZFSet_injective pair.1)
    have tail := ih pair.2
    funext i
    exact Fin.cases head (fun i => congrFun tail i) i

noncomputable def zfNatRelation {n : Nat} (relation : (Fin n → Nat) → Prop) : ZFSet.{u} :=
  ZFSet.range (fun tuple : {v : Fin n → Nat // relation v} => zfNatTuple tuple.val)

theorem zfNatRelation_mem {n : Nat} (relation : (Fin n → Nat) → Prop) (tuple : Fin n → Nat) :
    zfNatTuple.{u} tuple ∈ zfNatRelation relation ↔ relation tuple := by
  rw [zfNatRelation, ZFSet.mem_range]
  constructor
  · rintro ⟨other, same⟩
    exact zfNatTuple_injective same ▸ other.property
  · exact fun h => ⟨⟨tuple, h⟩, rfl⟩

theorem zfNatRelation_rank_le {n : Nat} (relation : (Fin n → Nat) → Prop) :
    (zfNatRelation.{u} relation).rank ≤ Ordinal.omega0 := by
  have included : zfNatRelation.{u} relation ⊆ ZFSet.vonNeumann Ordinal.omega0 := by
    intro z hz
    obtain ⟨tuple, rfl⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.mem_vonNeumann.mpr (zfNatTuple_rank_lt tuple.val)
  simpa only [ZFSet.rank_vonNeumann] using ZFSet.rank_mono included

noncomputable def rankNatRelation {lambda : Ordinal.{u}} (hw : Ordinal.omega0 < lambda)
    {n : Nat} (relation : (Fin n → Nat) → Prop) : RankDomain lambda :=
  ⟨zfNatRelation relation, (zfNatRelation_rank_le relation).trans_lt hw⟩

/-- Every syntax table on finite natural tuples is fixed by an embedding
with a genuine critical point. No coding table is postulated as fixed. -/
theorem rankNatRelation_fixed {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {j : RankElementaryEmbedding lambda} {critical : OrdinalDomain lambda}
    (cp : RankCriticalPoint j critical) (hw : Ordinal.omega0 < lambda)
    {n : Nat} (relation : (Fin n → Nat) → Prop) :
    j (rankNatRelation hw relation) = rankNatRelation hw relation :=
  rankCriticalPoint_fixes_rank hl cp ((zfNatRelation_rank_le relation).trans_lt (rankCriticalPoint_omega_lt hl cp))

def rankSyntaxArity (v : Fin 2 → Nat) : Prop :=
  ∃ phi : RankPureSyntax, v 0 = rankSyntaxCode phi ∧ v 1 = phi.1

def rankSyntaxFalse (v : Fin 1 → Nat) : Prop :=
  ∃ n, v 0 = rankSyntaxCode ⟨n, .falsum⟩

def rankSyntaxEqual (v : Fin 3 → Nat) : Prop :=
  ∃ (n : Nat) (x y : Fin n), v 0 = rankSyntaxCode ⟨n, .equal x y⟩ ∧ v 1 = x.val ∧ v 2 = y.val

def rankSyntaxMember (v : Fin 3 → Nat) : Prop :=
  ∃ (n : Nat) (x y : Fin n), v 0 = rankSyntaxCode ⟨n, .member x y⟩ ∧ v 1 = x.val ∧ v 2 = y.val

def rankSyntaxImp (v : Fin 3 → Nat) : Prop :=
  ∃ (n : Nat) (p q : RankPredicateFormula 0 n), v 0 = rankSyntaxCode ⟨n, .imp p q⟩ ∧
    v 1 = rankSyntaxCode ⟨n, p⟩ ∧ v 2 = rankSyntaxCode ⟨n, q⟩

def rankSyntaxAll (v : Fin 2 → Nat) : Prop :=
  ∃ (n : Nat) (p : RankPredicateFormula 0 (n + 1)), v 0 = rankSyntaxCode ⟨n, .all p⟩ ∧
    v 1 = rankSyntaxCode ⟨n + 1, p⟩

end FullMarkedBLP
