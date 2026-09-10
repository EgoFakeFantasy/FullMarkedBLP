import Mathlib.ModelTheory.ElementaryMaps
import FullMarkedBLP.ZFCSemantics

namespace FullMarkedBLP

/-- The first-order language has only the binary membership relation. -/
def membershipLanguage : FirstOrder.Language where
  Functions := fun _ => Empty
  Relations := fun n => PLift (n = 2)

instance rankDomainMembershipStructure (lambda : Ordinal.{u}) :
    membershipLanguage.Structure (RankDomain lambda) where
  funMap := fun f => Empty.elim f
  RelMap := fun {n} r xs => by
    obtain ⟨hn⟩ := r
    subst n
    exact (xs 0).val ∈ (xs 1).val

/-- Full first-order elementarity on V_lambda; no existence assertion. -/
abbrev RankElementaryEmbedding (lambda : Ordinal.{u}) :=
  FirstOrder.Language.ElementaryEmbedding membershipLanguage (RankDomain lambda) (RankDomain lambda)

theorem rankElementary_mem_iff {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    (x y : RankDomain lambda) : (j x).val ∈ (j y).val ↔ x.val ∈ y.val := by
  have h := j.map_rel (show membershipLanguage.Relations 2 from ⟨rfl⟩) ![x, y]
  simpa [FirstOrder.Language.Structure.RelMap, rankDomainMembershipStructure, Function.comp_def] using h

theorem rankElementary_injective {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda) :
    Function.Injective j := j.injective

end FullMarkedBLP
