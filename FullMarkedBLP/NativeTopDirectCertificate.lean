import FullMarkedBLP.NativeEmbeddingValues

namespace FullMarkedBLP

/-- Every actual new direct mark of the native top row has its literal
one-factor trace and natural weak certificate under the concrete candidates. -/
theorem rankRealization_native_top_direct_mark {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r j : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hn : native a r = some (b, sources))
    (hj : j < sources.length) :
    ∃ p delta, MarkTrace b (r + sources.length) (r + j) [r + j, p] ∧
      naturalCutoff (fun i => rankOrdinalAction (nativeEmbeddingValues embedding r sources.length i))
        (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length)
        [r + j, p].dropLast = some delta ∧
      rankCutoffAgreement delta.val (nativeEmbeddingValues embedding r sources.length (r + sources.length))
        (evalWord (fun i => (nativeEmbeddingValues embedding r sources.length i :
          RankDomain lambda → RankDomain lambda)) [r + j, p].dropLast) := by
  obtain ⟨p, ht⟩ := native_top_new_marks_have_trace h.valid hr (native_sources_of_success hn) hn hj
  let delta := nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources)
    r sources.length (r + j + 1)
  refine ⟨p, delta, ht, rfl, ?_⟩
  exact nativeEmbeddingValues_direct_certificate embedding r sources.length sources.length j
    (Nat.le_refl _) hj.le delta.val

end FullMarkedBLP

