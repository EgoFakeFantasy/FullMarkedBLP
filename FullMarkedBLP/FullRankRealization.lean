import FullMarkedBLP.MStarBoundaryPreservation
import FullMarkedBLP.ExpansionRankRealization

namespace FullMarkedBLP

/-- The manuscript's full same-domain semantic certificate: all row/mark
conditions and Sat, together with every complete finite linedness witness
between the fixed first-triple endpoints. Existence from I2 is separate. -/
structure RankFullMarkedRealization {lambda : Ordinal.{u}} (a : Pattern)
    (theta : Nat → OrdinalDomain lambda) (embedding : Nat → RankElementaryEmbedding lambda) : Prop where
  rows : RankMarkedRealization a theta embedding
  lined : RankAllFiniteLined (theta 0) (theta 1) (theta 2)

theorem rankAllFiniteLined_shortCopy {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) (lined : RankAllFiniteLined (theta 0) (theta 1) (theta 2))
    {last : Row} {p e : Nat} (copy : shortCopy a = some b)
    (lastAt : rowAt a a.length = some last) (hp : last.p = some p) (he : last.e = some e) :
    RankAllFiniteLined (shortCopyColumnValues theta (embedding a.length) a.length p 0)
      (shortCopyColumnValues theta (embedding a.length) a.length p 1)
      (shortCopyColumnValues theta (embedding a.length) a.length p 2) := by
  have columns := (rankRowRealization_shortCopy_boundaries hl h copy lastAt hp he).1
  simpa only [columns 0 (by omega), columns 1 (by omega), columns 2 (by omega)] using lined

/-- Cut keeps the whole witness family and strictly lowers the terminal. -/
theorem rankFullMarkedRealization_cut {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankFullMarkedRealization a theta embedding) (step : cut a = some b) :
    RankFullMarkedRealization b theta embedding ∧ theta (b.length + 1) < theta (a.length + 1) := by
  have size : 2 < a.length := by
    unfold cut at step
    split at step
    next hs => exact hs
    next => simp at step
  have same : b = a.dropLast := by simpa only [cut, if_pos size, Option.some.injEq] using step.symm
  have index : b.length + 1 = a.length := by simp [same]; omega
  refine ⟨⟨rankMarkedRealization_cut h.rows step, h.lined⟩, ?_⟩
  rw [index]
  exact h.rows.increasing a.length (a.length + 1) (by omega) le_rfl

/-- Every positive E parameter preserves the entire semantic certificate
and terminal, with success of the literal algorithm included. -/
theorem rankFullMarkedRealization_expand_total {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankFullMarkedRealization a theta embedding)
    (kind : classify a = .successor ∨ classify a = .limit) {k : Nat} (positive : 0 < k) :
    ∃ (b : Pattern) (newTheta : Nat → OrdinalDomain lambda) (newEmbedding : Nat → RankElementaryEmbedding lambda),
      expand a k = some b ∧ RankFullMarkedRealization b newTheta newEmbedding ∧
      (∀ i, i ≤ 2 → newTheta i = theta i) ∧
      newTheta (b.length + 1) = theta (a.length + 1) := by
  obtain ⟨b, newTheta, newEmbedding, step, rows, lined, columns, terminal, _⟩ :=
    rankMarkedRealization_expand_total hl h.rows h.lined kind positive
  obtain ⟨_, _, _, _, _, _, size, _⟩ := rankMarkedRealization_expansion_edges h.rows kind
  exact ⟨b, newTheta, newEmbedding, step, ⟨rows, lined⟩, fun i hi => columns i (by omega), terminal⟩

/-- Full M_star closure preserves the SAME complete witness family at the
unchanged first triple, in addition to every row/mark certificate. -/
theorem rankFullMarkedRealization_mStar {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankFullMarkedRealization a theta embedding) (step : mStar a = some b) :
    ∃ (newTheta : Nat → OrdinalDomain lambda) (newEmbedding : Nat → RankElementaryEmbedding lambda),
      RankFullMarkedRealization b newTheta newEmbedding ∧
      (∀ i, i ≤ 2 → newTheta i = theta i) ∧
      newTheta (b.length + 1) = theta (a.length + 1) := by
  obtain ⟨newTheta, newEmbedding, rows, columns, terminal, _⟩ :=
    rankMarkedRealization_mStar_boundaries hl h.rows step
  have lined : RankAllFiniteLined (newTheta 0) (newTheta 1) (newTheta 2) := by
    simpa only [columns 0 (by omega), columns 1 (by omega), columns 2 (by omega)] using h.lined
  exact ⟨newTheta, newEmbedding, ⟨rows, lined⟩, columns, terminal⟩

/-- Closure along every edge of the exact original Step relation. No
semantic acceptance filter is added. Cut lowers the terminal; the other
two operations preserve it, and all three retain the first triple. -/
theorem rankFullMarkedRealization_step {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankFullMarkedRealization a theta embedding) (step : Step a b) :
    ∃ (newTheta : Nat → OrdinalDomain lambda) (newEmbedding : Nat → RankElementaryEmbedding lambda),
      RankFullMarkedRealization b newTheta newEmbedding ∧
      (∀ i, i ≤ 2 → newTheta i = theta i) ∧
      newTheta (b.length + 1) ≤ theta (a.length + 1) := by
  cases step with
  | cut success =>
    obtain ⟨result, terminal⟩ := rankFullMarkedRealization_cut h success
    exact ⟨theta, embedding, result, fun _ _ => rfl, terminal.le⟩
  | expand positive success =>
    have kind : classify a = .successor ∨ classify a = .limit := by
      unfold expand at success
      split at success
      next kind => exact kind
      next => simp at success
    obtain ⟨out, newTheta, newEmbedding, computed, result, columns, terminal⟩ :=
      rankFullMarkedRealization_expand_total hl h kind positive
    have same := Option.some.inj (computed.symm.trans success)
    subst out
    exact ⟨newTheta, newEmbedding, result, columns, terminal.le⟩
  | marked success =>
    obtain ⟨newTheta, newEmbedding, result, columns, terminal⟩ := rankFullMarkedRealization_mStar hl h success
    exact ⟨newTheta, newEmbedding, result, columns, terminal.le⟩

/-- Conditional on the genuine standard-root certificate, all literal
generated states have full certificates on the original rank domain.
This theorem discharges generated-domain closure; the I2 root existence
and the final well-order theorem are NOT asserted here. -/
theorem rankFullMarkedRealization_generated {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda)
    {rootTheta : Nat → OrdinalDomain lambda} {rootEmbedding : Nat → RankElementaryEmbedding lambda}
    (root : RankFullMarkedRealization start rootTheta rootEmbedding)
    {a : Pattern} (generated : Generated a) :
    ∃ (theta : Nat → OrdinalDomain lambda) (embedding : Nat → RankElementaryEmbedding lambda),
      RankFullMarkedRealization a theta embedding ∧
      (∀ i, i ≤ 2 → theta i = rootTheta i) ∧
      theta (a.length + 1) ≤ rootTheta (start.length + 1) := by
  induction generated with
  | root => exact ⟨rootTheta, rootEmbedding, root, fun _ _ => rfl, le_rfl⟩
  | child generated step ih =>
    obtain ⟨theta, embedding, current, columns, terminal⟩ := ih
    obtain ⟨newTheta, newEmbedding, result, newColumns, newTerminal⟩ :=
      rankFullMarkedRealization_step hl current step
    exact ⟨newTheta, newEmbedding, result, fun i hi => (newColumns i hi).trans (columns i hi),
      newTerminal.trans terminal⟩

end FullMarkedBLP
