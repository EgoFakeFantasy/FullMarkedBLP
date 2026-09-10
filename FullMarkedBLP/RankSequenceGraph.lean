import FullMarkedBLP.RankFunctionSpace
import FullMarkedBLP.RankOmegaPreservation

namespace FullMarkedBLP

theorem zfFunctionGraph_congr {x y z : ZFSet.{u}} (f : x → y) (g : x → z)
    (same : ∀ a, (f a).val = (g a).val) : zfFunctionGraph f = zfFunctionGraph g := by
  unfold zfFunctionGraph
  congr 1
  funext a
  rw [same a]

noncomputable def rankFunctionGraph {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (x y : RankDomain lambda) (f : x.val → y.val) : RankDomain lambda :=
  ⟨zfFunctionGraph f, rank_function_lt_of_limit hl x.property y.property (zfFunctionGraph_isFunc f)⟩

theorem rankFunctionGraph_isFunction {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (x y : RankDomain lambda) (f : x.val → y.val) :
    rankIsFunction (rankFunctionGraph hl x y f) x y :=
  (rankIsFunction_iff hl _ _ _).mpr (zfFunctionGraph_isFunc f)

noncomputable def natZFSetOmegaEquiv : Nat ≃ Ordinal.omega0.{u}.toZFSet :=
  Equiv.ofBijective (fun n => ⟨(n : Ordinal.{u}).toZFSet,
    Ordinal.toZFSet_mem_toZFSet_iff.mpr (Ordinal.natCast_lt_omega0 n)⟩) (by
      constructor
      · intro m n same
        exact Nat.cast_injective (Ordinal.toZFSet_injective (congrArg Subtype.val same))
      · intro a
        obtain ⟨o, below, eqA⟩ := Ordinal.mem_toZFSet_iff.mp a.property
        obtain ⟨n, eqO⟩ := Ordinal.lt_omega0.mp below
        refine ⟨n, Subtype.ext ?_⟩
        change (n : Ordinal).toZFSet = a.val
        rw [← eqO]
        exact eqA)

/-- Countable sequences and actual functions from the von Neumann omega. -/
noncomputable def zfSequenceEquiv (target : ZFSet.{u}) :
    (Nat → target) ≃ ZFSet.funs Ordinal.omega0.toZFSet target :=
  (Equiv.arrowCongr natZFSetOmegaEquiv (Equiv.refl target)).trans
    (zfFunctionEquiv Ordinal.omega0.toZFSet target)

noncomputable def rankSequenceGraph {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (target : RankDomain lambda) (sequence : Nat → target.val) :
    RankDomain lambda :=
  rankFunctionGraph hl (ordinalDomainElement ⟨Ordinal.omega0, hw⟩) target
    (fun a => sequence (natZFSetOmegaEquiv.symm a))

theorem rankSequenceGraph_isFunction {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (target : RankDomain lambda) (sequence : Nat → target.val) :
    rankIsFunction (rankSequenceGraph hl hw target sequence)
      (ordinalDomainElement ⟨Ordinal.omega0, hw⟩) target :=
  rankFunctionGraph_isFunction hl _ _ _

theorem rankSequenceGraph_congr {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (x y : RankDomain lambda)
    (f : Nat → x.val) (g : Nat → y.val) (same : ∀ n, (f n).val = (g n).val) :
    rankSequenceGraph hl hw x f = rankSequenceGraph hl hw y g :=
  Subtype.ext (zfFunctionGraph_congr _ _ (fun a => same (natZFSetOmegaEquiv.symm a)))

end FullMarkedBLP
