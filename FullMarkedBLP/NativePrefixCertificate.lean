import FullMarkedBLP.NativePrefixEdges

namespace FullMarkedBLP

theorem rankRealization_native_prefix_mark {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r p e owner y : Nat} {nativeRow row : Row} {sources : List Nat}
    (hr : rowAt a r = some nativeRow) (hp : nativeRow.p = some p) (he : nativeRow.e = some e)
    (hn : native a r = some (b, sources)) (ho : owner < r)
    (hrow : rowAt a owner = some row) (hy : y ∈ row.marks)
    (freshEmbedding : Nat → RankElementaryEmbedding lambda) :
    ∃ xs delta, MarkTrace b owner y xs ∧
      naturalCutoff
        (fun i => rankOrdinalAction (nativeColumnValues embedding freshEmbedding r sources.length i))
        (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length)
        xs.dropLast = some delta ∧
      rankCutoffAgreement delta.val
        ((nativeColumnValues embedding freshEmbedding r sources.length owner :
          RankElementaryEmbedding lambda) : RankDomain lambda → RankDomain lambda)
        (evalWord (fun i => ((nativeColumnValues embedding freshEmbedding r sources.length i :
          RankElementaryEmbedding lambda) : RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
  obtain ⟨k, s, xs, oldDelta, hk, hky, hks, ht, hd, hc⟩ := h.marked owner row y hrow hy
  have hyr := (h.proper owner row hrow).2 y hy
  have hmap : xs.map (shiftAfter r sources.length) = xs := by
    conv_rhs => rw [← List.map_id xs]
    apply List.map_congr_left
    intro x hx
    have hxb := trace_member_le_head h.valid ht hx
    simp only [shiftAfter, if_neg (show ¬ r < x by omega), id_eq]
  have hdrop : xs.dropLast.map (shiftAfter r sources.length) = xs.dropLast := by
    rw [List.map_dropLast, hmap]
  obtain ⟨delta, hdelta, hcert⟩ := rankRealization_native_old_certificate h hr hp he
    (native_sources_of_success hn) freshEmbedding (embedding owner) xs.dropLast hd hc
  refine ⟨xs, delta, ?_, ?_, ?_⟩
  · exact ⟨row, k, s, (native_prefix_rowAt hn ho).trans hrow, hy, hk, hky, hks,
      native_prefix_trace h.valid hn ht (by omega)⟩
  · simpa only [hdrop] using hdelta
  · rw [nativeColumnValues_before embedding freshEmbedding (by omega : owner ≤ r)]
    simpa only [hdrop] using hcert

end FullMarkedBLP




