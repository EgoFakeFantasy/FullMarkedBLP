import FullMarkedBLP.HistoricalSatEndpointCap
import FullMarkedBLP.CopyPrefixValues

namespace FullMarkedBLP

/-- The actual eligible scan owner after a Sat short copy has its native
entrance B bounded by the full predecessor record. This uses the original
copied-region witness, not current global Sat. -/
theorem shortCopy_scan_owner_endpoint_cap {lambda : Ordinal.{u}} {parent copied a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r base e : Nat}
    {lowerSources : List Nat}
    (parentValid : ∀ i row, rowAt parent i = some row → row.CoreValid i)
    (sat : Sat parent) (copy : shortCopy parent = some copied)
    (reach : ScanRankReach copied initialTheta initialEmbedding a rec r theta embedding)
    (entryReal : RankRowRealization copied initialTheta initialEmbedding)
    (currentReal : RankRowRealization a theta embedding)
    (verified : ScanPriorVerifiedEvents copied initialTheta initialEmbedding r)
    {row : Row} (hr : rowAt a r = some row) (hp : row.p = some base) (he : row.e = some e)
    (eligible : row.core.length ≤ 2 * row.step) (record : (base, lowerSources) ∈ rec) :
    ∃ w, (rowAt a e).bind Row.b = some w ∧ w ≤ base + lowerSources.length := by
  obtain ⟨phi, original, mono, zero, lengths, holds, tail, rows, records, intervals⟩ :=
    scanRankReach_original_b_intervals reach entryReal
  have bands := intervals (scanPriorVerifiedEvents_geometry verified)
    (scanPriorVerifiedEvents_endpoint_transport verified) verified
  have owner : phi original = r := by simpa using tail 0
  have rb := rowAt_bounds hr
  have positive : 0 < original := by
    by_cases eq : original = 0
    · rw [eq, zero] at owner; omega
    · omega
  obtain ⟨entry, atEntry⟩ := rowAt_exists (a := copied) positive (by omega)
  have mapped := rows original entry (Nat.le_refl _) atEntry
  rw [owner, hr] at mapped
  have shape := Option.some.inj mapped
  have valid := entryReal.valid original entry atEntry
  have room := Row.step_lt_length valid.2.2.2
  obtain ⟨lower, lowerAt⟩ := fromRight_exists (xs := entry.core) (k := entry.step + 1) (by omega) (by omega)
  have lowerP : entry.p = some lower := lowerAt
  have lowerMap : phi lower = base := by
    have mappedP : row.p = some (phi lower) := by
      rw [shape]
      change fromRight (entry.core.map phi) (entry.step + 1) = some (phi lower)
      rw [fromRight_map]
      change entry.p.map phi = some (phi lower)
      simp only [lowerP, Option.map_some]
    exact Option.some.inj (mappedP.symm.trans hp)
  have lowerOwner : lower < original := fromRight_lt_last valid.1 valid.2.2.1
    (by have := valid.2.2.2.1; omega : 1 < entry.step + 1) lowerAt
  have copiedRegion : parent.length ≤ lower := by
    by_cases bound : parent.length ≤ lower
    · exact bound
    · have prefixValues := shortCopy_scan_prefix_values parentValid sat copy reach lower (by omega)
      have below : phi lower < r := by rw [← owner]; exact mono lowerOwner
      have extensive : ∀ i, i ≤ phi i := by
        intro i; induction i with
        | zero => omega
        | succ i ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (mono (Nat.lt_succ_self i)))
      have same := realized_column_index_eq currentReal (by omega : phi lower ≤ a.length + 1)
        (by have := extensive lower; omega : lower ≤ a.length + 1)
        ((holds lower).1.trans prefixValues.1.symm)
      have region := (shortCopy_scan_record_region parentValid sat copy
        (scanEmbeddingReach_forget (scanRankReach_embeddings reach))).2 (base, lowerSources) record
      dsimp only at region
      omega
  have oldEligible : entry.core.length ≤ 2 * entry.step := by
    simpa only [shape, List.length_map] using eligible
  obtain ⟨oldE, er, v, oldEAt, atEr, atV, vBound⟩ :=
    shortCopy_internal_sat parentValid sat copy atEntry lowerP copiedRegion oldEligible
  have endpointMap : phi oldE = e := by
    have mappedE : row.e = some (phi oldE) := by
      rw [shape]
      change fromRight (entry.core.map phi) entry.step = some (phi oldE)
      rw [fromRight_map]
      change entry.e.map phi = some (phi oldE)
      simp only [oldEAt, Option.map_some]
    exact Option.some.inj (mappedE.symm.trans he)
  obtain ⟨w, actual, _, upper⟩ := bands oldE er v atEr atV
  obtain ⟨i, _, lowerImage, successor⟩ := records base lowerSources record
  have same : i = lower := mono.injective (lowerImage.trans lowerMap.symm)
  subst i
  have cap : phi (v + 1) ≤ phi (lower + 1) := mono.monotone (by omega)
  rw [successor] at cap
  exact ⟨w, by simpa only [endpointMap] using actual, by omega⟩

end FullMarkedBLP


