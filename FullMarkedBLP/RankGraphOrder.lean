import FullMarkedBLP.RankSequenceGraph
import FullMarkedBLP.RankApplicationComposition

namespace FullMarkedBLP
open FirstOrder Language

/-- Preservation and reflection of membership on the graph's inputs. -/
def RankGraphOrderEmbedding {lambda : Ordinal.{u}} (graph : RankDomain lambda) : Prop :=
  ∀ a b x y : RankDomain lambda, rankGraphApplies graph a x → rankGraphApplies graph b y →
    (a.val ∈ b.val ↔ x.val ∈ y.val)

def rankGraphOrderEmbeddingFormula : membershipLanguage.Formula (Fin 1) :=
  .all (.all (.all (.all ((rankGraphAppliesAt (.inl 0) (.inr 0) (.inr 2)).imp
    ((rankGraphAppliesAt (.inl 0) (.inr 1) (.inr 3)).imp
      ((rankMemAt (.inr 0) (.inr 1)).iff (rankMemAt (.inr 2) (.inr 3))))))))

theorem rankGraphOrderEmbeddingFormula_realize {lambda : Ordinal.{u}} (graph : RankDomain lambda) :
    rankGraphOrderEmbeddingFormula.Realize ![graph] ↔ RankGraphOrderEmbedding graph := by
  simp [rankGraphOrderEmbeddingFormula, Formula.Realize, BoundedFormula.Realize,
    rankMemAt_realize, rankGraphAppliesAt_realize, RankGraphOrderEmbedding, Fin.snoc]

theorem rankElementary_graphOrderEmbedding_iff {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (graph : RankDomain lambda) :
    RankGraphOrderEmbedding (j graph) ↔ RankGraphOrderEmbedding graph := by
  have result := j.map_formula rankGraphOrderEmbeddingFormula ![graph]
  have same : j ∘ ![graph] = ![j graph] := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  rw [same, rankGraphOrderEmbeddingFormula_realize, rankGraphOrderEmbeddingFormula_realize] at result
  exact result

theorem rankFunctionGraph_applies_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (x y : RankDomain lambda) (f : x.val → y.val) (a b : RankDomain lambda) :
    rankGraphApplies (rankFunctionGraph hl x y f) a b ↔
      ∃ ha : a.val ∈ x.val, (f ⟨a.val, ha⟩).val = b.val := by
  rw [rankGraphApplies_iff hl]
  exact mem_zfFunctionGraph f a.val b.val

theorem rankFunctionGraph_orderEmbedding {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (x y : RankDomain lambda) (f : x.val → y.val)
    (ordered : ∀ a b, (f a).val ∈ (f b).val ↔ a.val ∈ b.val) :
    RankGraphOrderEmbedding (rankFunctionGraph hl x y f) := by
  intro a b c d ac bd
  obtain ⟨ha, hc⟩ := (rankFunctionGraph_applies_iff hl x y f a c).mp ac
  obtain ⟨hb, hd⟩ := (rankFunctionGraph_applies_iff hl x y f b d).mp bd
  rw [← hc, ← hd]
  exact (ordered ⟨a.val, ha⟩ ⟨b.val, hb⟩).symm

theorem rankFunctionGraph_composes {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (x y z : RankDomain lambda) (f : x.val → y.val) (g : y.val → z.val) :
    RankGraphComposes (rankFunctionGraph hl y z g) (rankFunctionGraph hl x y f)
      (rankFunctionGraph hl x z (g ∘ f)) := by
  intro a b c ab bc
  obtain ⟨ha, hb⟩ := (rankFunctionGraph_applies_iff hl x y f a b).mp ab
  obtain ⟨hb', hc⟩ := (rankFunctionGraph_applies_iff hl y z g b c).mp bc
  apply (rankFunctionGraph_applies_iff hl x z (g ∘ f) a c).mpr
  refine ⟨ha, ?_⟩
  have same : f ⟨a.val, ha⟩ = ⟨b.val, hb'⟩ := Subtype.ext hb
  change (g (f ⟨a.val, ha⟩)).val = c.val
  rw [same]
  exact hc

end FullMarkedBLP
