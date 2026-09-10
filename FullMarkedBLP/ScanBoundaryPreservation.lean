import FullMarkedBLP.CopyFullScanClosure

namespace FullMarkedBLP

/-- No positive native source can lie strictly below row 1. This needs
only valid cores, not a prescribed literal first row or Sat. -/
theorem nativeSources_first_empty {a : Pattern} {row : Row} {sources : List Nat}
    (valid : ∀ r rw, rowAt a r = some rw → rw.CoreValid r)
    (hr : rowAt a 1 = some row) (hs : nativeSources a 1 = some sources) : sources = [] := by
  unfold nativeSources at hs
  rw [hr] at hs
  dsimp only [Bind.bind, Option.bind] at hs
  split at hs
  next => exact (Option.some.inj hs).symm
  next =>
    obtain ⟨p, _, hs⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨e, he, hs⟩ := Option.bind_eq_some_iff.mp hs
    have hv := valid 1 row hr
    have eb := fromRight_le_last hv.1 hv.2.2.1 hv.2.2.2.1 he
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have bounds := nativeSourcesFuel_bounds valid hs x hx
    omega

theorem nativeColumnValues_terminal {alpha : Type u} (old fresh : Nat → alpha)
    {n r : Nat} (t : Nat) (bound : r ≤ n) :
    nativeColumnValues old fresh r t (n + t + 1) = old (n + 1) := by
  rw [nativeColumnValues, if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

theorem nativeEmbeddingValues_last {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) {n r : Nat} (t : Nat) (bound : r ≤ n) :
    nativeEmbeddingValues embedding r t (n + t) = embedding n := by
  by_cases same : r = n
  · subst r
    exact nativeEmbeddingValues_block embedding n t t le_rfl
  · have shifted : shiftAfter r t n = n + t := by simp [shiftAfter, show r < n by omega]
    rw [← shifted]
    exact nativeEmbeddingValues_old embedding r t n

/-- Both semantic boundary values are invariant under the actual scan,
including a nonempty native block at the last row. -/
theorem scanRankReach_terminal_and_last {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding) :
    theta (a.length + 1) = initialTheta (initial.length + 1) ∧
      embedding a.length = initialEmbedding initial.length := by
  induction reach with
  | start => exact ⟨rfl, rfl⟩
  | @next before after history owner sources oldTheta oldEmbedding prior bound birth ih =>
    have length := native_length birth
    rw [completeFrozenMarks_length] at length
    rw [length, nativeColumnValues_terminal _ _ _ bound, nativeEmbeddingValues_last _ _ bound]
    exact ih

/-- Valid completed entrance cores force the first scan step to insert no
columns. Every subsequent step preserves columns 0, 1 and 2 directly. -/
theorem scanRankReach_first_three {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding) :
    ∀ i, i ≤ 2 → theta i = initialTheta i := by
  induction reach with
  | start => intro _ _; rfl
  | @next before after history owner sources oldTheta oldEmbedding prior bound birth ih =>
    intro i hi
    have forgotten := scanEmbeddingReach_forget (scanRankReach_embeddings prior)
    have positive := (scanReach_records_before forgotten).1
    by_cases later : 2 ≤ owner
    · rw [nativeColumnValues_before _ _ (by omega : i ≤ owner)]
      exact ih i hi
    · have ownerEq : owner = 1 := by omega
      have hs := native_sources_of_success birth
      obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp birth
      have empty : sources = [] := by
        apply nativeSources_first_empty (historyValid before history owner forgotten)
        · simpa only [ownerEq] using hr
        · simpa only [ownerEq] using hs
      simpa only [empty, List.length_nil, nativeColumnValues_zero] using ih i hi

/-- Full scan closure with the concrete boundary assignments tracked.
The realization and all boundary equalities belong to the SAME output
assignment, obtained from the actual labelled scan history. -/
theorem shortCopy_fullScan_total_preserves_boundaries {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {parent copied : Pattern}
    {initialTheta : Nat → OrdinalDomain lambda}
    {initialEmbedding : Nat → RankElementaryEmbedding lambda}
    (parentValid : ∀ i row, rowAt parent i = some row → row.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (entryReal : RankRowRealization copied initialTheta initialEmbedding) :
    ∃ (b : Pattern) (theta : Nat → OrdinalDomain lambda) (embedding : Nat → RankElementaryEmbedding lambda),
      fullScan copied = some b ∧ RankMarkedRealization b theta embedding ∧
      (∀ i, i ≤ 2 → theta i = initialTheta i) ∧
      theta (b.length + 1) = initialTheta (copied.length + 1) ∧
      embedding b.length = initialEmbedding copied.length := by
  have historyValid : ∀ before history owner, ScanReach copied before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i := by
    intro before history owner prior
    obtain ⟨theta, embedding, labelled⟩ := scanReach_rank_lift prior initialTheta initialEmbedding
    have result := shortCopy_scan_realization hl parentValid sat copy entryReal labelled
    cases hr : rowAt before owner with
    | none => simpa only [completeFrozenMarks, hr] using result.1.valid
    | some row => exact (result.2 row hr).1.valid
  obtain ⟨b, success, saturated⟩ := fullScan_total_sat_of_history_valid historyValid
  obtain ⟨rec, cursor, reach, _, _⟩ := fullScan_reaches_end success
  obtain ⟨theta, embedding, labelled⟩ := scanReach_rank_lift reach initialTheta initialEmbedding
  have result := shortCopy_scan_realization hl parentValid sat copy entryReal labelled
  exact ⟨b, theta, embedding, success, rankRowRealization_with_sat result.1 saturated,
    scanRankReach_first_three historyValid labelled, scanRankReach_terminal_and_last labelled⟩

end FullMarkedBLP
