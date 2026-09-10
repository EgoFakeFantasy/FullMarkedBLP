import FullMarkedBLP.NativeSuffixEdges

namespace FullMarkedBLP

theorem rankRealization_native_suffix_mark {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r p e owner y : Nat} {nativeRow row : Row} {sources : List Nat}
    (hr : rowAt a r = some nativeRow) (hp : nativeRow.p = some p) (he : nativeRow.e = some e)
    (hn : native a r = some (b, sources)) (ho : r < owner)
    (hrow : rowAt a owner = some row) (hy : y ∈ row.marks)
    (freshEmbedding : Nat → RankElementaryEmbedding lambda) :
    ∃ xs delta, MarkTrace b (owner + sources.length) (shiftAfter r sources.length y) xs ∧
      naturalCutoff
        (fun i => rankOrdinalAction (nativeColumnValues embedding freshEmbedding r sources.length i))
        (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length)
        xs.dropLast = some delta ∧
      rankCutoffAgreement delta.val
        ((nativeColumnValues embedding freshEmbedding r sources.length (owner + sources.length) : RankElementaryEmbedding lambda) : RankDomain lambda → RankDomain lambda)
        (evalWord (fun i => ((nativeColumnValues embedding freshEmbedding r sources.length i :
          RankElementaryEmbedding lambda) : RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
  obtain ⟨xs, oldDelta, ht, hd, _, _, hc⟩ := rankRealization_mark_certificate h hrow hy
  obtain ⟨delta, hdelta, hcert⟩ := rankRealization_native_old_certificate h hr hp he
    (native_sources_of_success hn) freshEmbedding (embedding owner) xs.dropLast hd hc
  refine ⟨xs.map (shiftAfter r sources.length), delta,
    native_suffix_markTrace h.valid hn ht ho, ?_, ?_⟩
  · simpa only [List.map_dropLast] using hdelta
  · have hei : owner + sources.length = shiftAfter r sources.length owner := by
      simp only [shiftAfter, if_pos ho]
    rw [hei, nativeColumnValues_preserves]
    simpa only [List.map_dropLast] using hcert

end FullMarkedBLP



