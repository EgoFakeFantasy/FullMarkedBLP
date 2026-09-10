import FullMarkedBLP.NativeFreshOrder

namespace FullMarkedBLP

theorem nativeColumnValues_strict {alpha : Type u} [Preorder alpha]
    (old fresh : Nat → alpha) (r t bound : Nat) (hr : r < bound)
    (oldStrict : ∀ i j, i < j → j ≤ bound → old i < old j)
    (freshStrict : ∀ i j, i < j → j < t → fresh i < fresh j)
    (lower : ∀ k, k < t → old r < fresh k)
    (upper : ∀ k, k < t → fresh k < old (r + 1))
    {i j : Nat} (hij : i < j) (hj : j ≤ bound + t) :
    nativeColumnValues old fresh r t i < nativeColumnValues old fresh r t j := by
  have oldLe : ∀ x y, x ≤ y → y ≤ bound → old x ≤ old y := by
    intro x y hxy hy
    rcases eq_or_lt_of_le hxy with he | he
    · subst y; exact le_rfl
    · exact (oldStrict x y he hy).le
  unfold nativeColumnValues
  by_cases hi : i ≤ r
  · rw [if_pos hi]
    by_cases hjr : j ≤ r
    · rw [if_pos hjr]
      exact oldStrict i j hij (by omega)
    · rw [if_neg hjr]
      by_cases hjt : j ≤ r + t
      · rw [if_pos hjt]
        exact lt_of_le_of_lt (oldLe i r hi (by omega)) (lower (j - r - 1) (by omega))
      · rw [if_neg hjt]
        exact oldStrict i (j - t) (by omega) (by omega)
  · rw [if_neg hi, if_neg (show ¬ j ≤ r by omega)]
    by_cases hit : i ≤ r + t
    · rw [if_pos hit]
      by_cases hjt : j ≤ r + t
      · rw [if_pos hjt]
        exact freshStrict (i - r - 1) (j - r - 1) (by omega) (by omega)
      · rw [if_neg hjt]
        exact lt_of_lt_of_le (upper (i - r - 1) (by omega))
          (oldLe (r + 1) (j - t) (by omega) (by omega))
    · rw [if_neg hit, if_neg (show ¬ j ≤ r + t by omega)]
      exact oldStrict (i - t) (j - t) (by omega) (by omega)

theorem rankRealization_native_columns_strict {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding)
    {r p e i j : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hn : nativeSources a r = some sources) (hij : i < j)
    (hj : j ≤ a.length + 1 + sources.length) :
    nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length i <
      nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length j := by
  apply nativeColumnValues_strict theta _ r sources.length (a.length + 1)
    (by have := (rowAt_bounds hr).2; omega) h.increasing
    (fun i j hij hj => rankRealization_native_fresh_strict h hr hn hij hj)
    (fun k hk => rankRealization_native_fresh_lower h hr hp he hn hk)
    (fun k _ => rankRealization_native_fresh_upper h hr hp he hn k) hij hj

end FullMarkedBLP

