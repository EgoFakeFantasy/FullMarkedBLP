import FullMarkedBLP.RankApplicationCritical

namespace FullMarkedBLP

/-- A complete finite linedness witness, with both endpoints fixed. The
factor numbered i realizes critical → point i → point (i+1). Every factor
is a genuine elementary embedding of the same rank domain. -/
structure RankLinedWitness {lambda : Ordinal.{u}} (k : Nat)
    (critical left right : OrdinalDomain lambda) where
  point : Nat → OrdinalDomain lambda
  factor : Nat → RankElementaryEmbedding lambda
  positive : 0 < k
  critical_lt : critical < left
  start : point 0 = left
  finish : point k = right
  increasing : ∀ i j, i < j → j ≤ k → point i < point j
  criticalPoint : ∀ i, i < k → RankCriticalPoint (factor i) critical
  firstEdge : ∀ i, i < k → rankOrdinalAction (factor i) critical = point i
  secondEdge : ∀ i, i < k → rankOrdinalAction (factor i) (point i) = point (i + 1)

/-- The manuscript requires an entire complete witness for each positive
finite length, always between the same two endpoints. -/
def RankAllFiniteLined {lambda : Ordinal.{u}} (critical left right : OrdinalDomain lambda) : Prop :=
  ∀ k, 0 < k → Nonempty (RankLinedWitness k critical left right)

/-- Actual application transports a complete witness, including its final
endpoint; it does not truncate a longer witness. -/
noncomputable def RankLinedWitness.apply {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (outer : RankElementaryEmbedding lambda)
    {k : Nat} {critical left right : OrdinalDomain lambda}
    (w : RankLinedWitness k critical left right) :
    RankLinedWitness k (rankOrdinalAction outer critical)
      (rankOrdinalAction outer left) (rankOrdinalAction outer right) where
  point i := rankOrdinalAction outer (w.point i)
  factor i := rankApply hl outer (w.factor i)
  positive := w.positive
  critical_lt := rankOrdinalAction_strictMono outer w.critical_lt
  start := congrArg (rankOrdinalAction outer) w.start
  finish := congrArg (rankOrdinalAction outer) w.finish
  increasing i j hij hj := rankOrdinalAction_strictMono outer (w.increasing i j hij hj)
  criticalPoint i hi := rankApply_criticalPoint hl outer (w.criticalPoint i hi)
  firstEdge i hi := (rankApply_ordinal_image hl outer (w.factor i) critical).trans
    (congrArg (rankOrdinalAction outer) (w.firstEdge i hi))
  secondEdge i hi := (rankApply_ordinal_image hl outer (w.factor i) (w.point i)).trans
    (congrArg (rankOrdinalAction outer) (w.secondEdge i hi))

theorem rankAllFiniteLined_apply {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (outer : RankElementaryEmbedding lambda)
    {critical left right : OrdinalDomain lambda} (h : RankAllFiniteLined critical left right) :
    RankAllFiniteLined (rankOrdinalAction outer critical)
      (rankOrdinalAction outer left) (rankOrdinalAction outer right) := by
  intro k hk
  obtain ⟨w⟩ := h k hk
  exact ⟨w.apply hl outer⟩

end FullMarkedBLP
