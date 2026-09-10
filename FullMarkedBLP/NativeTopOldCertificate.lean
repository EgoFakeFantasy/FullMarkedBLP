import FullMarkedBLP.NativeTopDirectCertificate

namespace FullMarkedBLP

theorem rankRealization_native_top_old_mark {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r p e y : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hn : native a r = some (b, sources)) (hne : sources ≠ []) (hy : y ∈ row.marks) :
    ∃ xs delta, MarkTrace b (r + sources.length) y xs ∧
      naturalCutoff (fun i => rankOrdinalAction (nativeEmbeddingValues embedding r sources.length i))
        (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length)
        xs.dropLast = some delta ∧
      rankCutoffAgreement delta.val (nativeEmbeddingValues embedding r sources.length (r + sources.length))
        (evalWord (fun i => (nativeEmbeddingValues embedding r sources.length i :
          RankDomain lambda → RankDomain lambda)) xs.dropLast) := by
  obtain ⟨k, s, xs, oldDelta, hk, hky, hks, ht, hd, hc⟩ := h.marked r row y hr hy
  have hyr := (h.proper r row hr).2 y hy
  have hmap : xs.map (shiftAfter r sources.length) = xs := by
    conv_rhs => rw [← List.map_id xs]
    apply List.map_congr_left
    intro x hx
    have hxb := trace_member_le_head h.valid ht hx
    simp only [shiftAfter, if_neg (show ¬ r < x by omega), id_eq]
  have hdrop : xs.dropLast.map (shiftAfter r sources.length) = xs.dropLast := by
    rw [List.map_dropLast, hmap]
  obtain ⟨delta, hdelta, hcert⟩ := rankRealization_native_old_certificate h hr hp he
    (native_sources_of_success hn) (fun _ => embedding r) (embedding r) xs.dropLast hd hc
  refine ⟨xs, delta, native_top_old_markTrace h.valid hr (h.proper r row hr)
    (native_sources_of_success hn) hn hne ⟨row, k, s, hr, hy, hk, hky, hks, ht⟩, ?_, ?_⟩
  · simpa only [nativeEmbeddingValues, hdrop] using hdelta
  · rw [nativeEmbeddingValues_block embedding r sources.length sources.length (Nat.le_refl _)]
    simpa only [nativeEmbeddingValues, hdrop] using hcert

end FullMarkedBLP

