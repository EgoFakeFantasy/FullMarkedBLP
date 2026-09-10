import FullMarkedBLP.RankElementaryMatrix
import FullMarkedBLP.RankRootFixedSyntax

namespace FullMarkedBLP

/-- Elementary-embedding graphs have a genuine finite Sigma-one class
definition with actual low-rank set parameters. Nontriviality and the finite
application-root equation are separate remaining parts of RankRootExists. -/
theorem rankElementaryGraph_lowRankDefinable {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (hw : Ordinal.omega0 < lambda) :
    RankSigmaOneClassLowRankDefinable
      (fun graph => ∃ j : RankElementaryEmbedding lambda, rankEmbeddingClassGraph j = graph) := by
  refine ⟨6, rankSyntaxBooks hw, rankSyntaxBooks_rank_le hw, 1, rankElementaryMatrix, ?_⟩
  exact rankElementaryGraph_sigmaOne hl hw

end FullMarkedBLP
