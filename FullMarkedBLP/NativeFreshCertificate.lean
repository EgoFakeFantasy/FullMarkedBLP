import FullMarkedBLP.NativeImageColumns

namespace FullMarkedBLP

/-- Total indexing of the concrete source images; unused indices return the
old owner column. Only indices below sources.length enter the inserted block. -/
noncomputable def nativeFreshValues {lambda : Ordinal.{u}}
    (theta : Nat → OrdinalDomain lambda) (owner : RankElementaryEmbedding lambda)
    (r : Nat) (sources : List Nat) (k : Nat) : OrdinalDomain lambda :=
  ((nativeImageColumns theta owner sources)[k]?).getD (theta r)

theorem rankRealization_native_fresh_upper {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r p e : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hn : nativeSources a r = some sources) (k : Nat) :
    nativeFreshValues theta (embedding r) r sources k < theta (r + 1) := by
  unfold nativeFreshValues
  cases hk : (nativeImageColumns theta (embedding r) sources)[k]? with
  | none =>
    simp only [Option.getD_none]
    exact h.increasing r (r + 1) (by omega) (by have := (rowAt_bounds hr).2; omega)
  | some value =>
    simp only [Option.getD_some]
    exact (rankRealization_native_images_gap h hr hp he hn value (List.mem_of_getElem? hk)).2

/-- For every old word certificate, the actual native source images give a
new natural cutoff and a transported certificate. Fresh row embeddings are
parameters because their own realization is a separate obligation. -/
theorem rankRealization_native_old_certificate {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r p e : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hs : nativeSources a r = some sources)
    (freshEmbedding : Nat → RankElementaryEmbedding lambda)
    (owner : RankElementaryEmbedding lambda) (word : List Nat)
    {oldDelta : OrdinalDomain lambda}
    (ho : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta word = some oldDelta)
    (certificate : rankCutoffAgreement oldDelta.val owner
      (evalWord (fun i => (embedding i : RankDomain lambda → RankDomain lambda)) word)) :
    ∃ newDelta, naturalCutoff
      (fun i => rankOrdinalAction (nativeColumnValues embedding freshEmbedding r sources.length i))
      (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length)
      (word.map (shiftAfter r sources.length)) = some newDelta ∧
      rankCutoffAgreement newDelta.val owner
        (evalWord (fun i => ((nativeColumnValues embedding freshEmbedding r sources.length i :
          RankElementaryEmbedding lambda) : RankDomain lambda → RankDomain lambda))
          (word.map (shiftAfter r sources.length))) := by
  have hw : word ≠ [] := by intro heq; simp [heq, naturalCutoff] at ho
  obtain ⟨newDelta, hd⟩ := naturalCutoff_defined
    (fun i => rankOrdinalAction (nativeColumnValues embedding freshEmbedding r sources.length i))
    (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length)
    (word := word.map (shiftAfter r sources.length)) (by simpa using hw)
  refine ⟨newDelta, hd, ?_⟩
  exact rankCertificate_native_values embedding freshEmbedding theta
    (nativeFreshValues theta (embedding r) r sources) r sources.length word owner
    (fun _ => (rankRealization_native_fresh_upper h hr hp he hs 0).le) ho hd certificate

end FullMarkedBLP

