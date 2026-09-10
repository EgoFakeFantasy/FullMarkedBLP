import FullMarkedBLP.FrozenPreservesEndpoint

namespace FullMarkedBLP

/-- A current row's e lies above the entire retained block at its predecessor. -/
theorem scanRankReach_e_above_predecessor_block {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r base e : Nat}
    {sources : List Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    {row : Row} (hr : rowAt a r = some row) (valid : row.CoreValid r)
    (hp : row.p = some base) (he : row.e = some e) (record : (base, sources) ∈ rec) :
    base + sources.length < e := by
  have pe := row_p_lt_e valid hp he
  have mem : e ∈ row.core := by
    unfold Row.e fromRight at he
    split at he
    · exact List.mem_of_getElem? he
    · simp at he
  exact scanRankReach_current_record_gap reach hr record
    (List.mem_append.mpr (Or.inl mem)) pe

/-- The bound survives full frozen completion to the actual native entrance. -/
theorem scanRankReach_completed_e_above_predecessor_block {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r base e : Nat}
    {sources : List Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (h : RankRowRealization a theta embedding)
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    {row out : Row} (hr : rowAt a r = some row) (hp : row.p = some base) (he : row.e = some e)
    (record : (base, sources) ∈ rec)
    (events : ∀ done mark suffix, row.marks = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current y => completeMark current rec r y) a) rec r mark theta embedding)
    (hout : rowAt (completeFrozenMarks a rec r) r = some out) :
    out.e = some e ∧ base + sources.length < e := by
  exact ⟨completeFrozenMarks_preserves_e historyValid
    (scanEmbeddingReach_forget (scanRankReach_embeddings reach)) h hr he events hout,
    scanRankReach_e_above_predecessor_block reach hr (h.valid r row hr) hp he record⟩

end FullMarkedBLP
