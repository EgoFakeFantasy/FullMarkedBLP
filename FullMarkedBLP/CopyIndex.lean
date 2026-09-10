import FullMarkedBLP.CopyOwner

namespace FullMarkedBLP

theorem core_head_le_entry {row : Row} {n minimum x k : Nat}
    (hv : row.CoreValid n) (hm : row.core.head? = some minimum)
    (hx : row.core[k]? = some x) : minimum ≤ x := by
  have hm' : row.core[0]? = some minimum := by simpa [List.head?_eq_getElem?] using hm
  by_cases h : x < minimum
  · have hh := sorted_index_lt_of_value_lt hv.1 hx hm' h; omega
  · omega

theorem copyEntry_high_value {n p x v : Nat} {row : Row}
    (hv : row.CoreValid n) (hp : row.p = some p) (hpx : p ≤ x)
    (h : copyEntry n row x = some v) : v = x + (n - p) := by
  obtain ⟨minimum, p', e, hm, hp', _, _, _, hcases⟩ := copyEntry_cases h
  have he := Option.some.inj (hp'.symm.trans hp)
  subst p'
  have hl := Row.step_lt_length hv.2.2.2
  have hpi : row.core[row.core.length - (row.step + 1)]? = some p := by
    simpa [Row.p, fromRight, show row.step + 1 ≤ row.core.length by omega] using hp
  have hmin := core_head_le_entry hv hm hpi
  rcases hcases with ⟨hlo, _⟩ | ⟨_, _, hv⟩ | ⟨_, hmid, _⟩
  · omega
  · exact hv
  · omega

theorem shortCopySources_description {row : Row} {sources : List Nat}
    (h : shortCopySources row = some sources) :
    ∃ p e, row.p = some p ∧ row.e = some e ∧ p ≠ 0 ∧
      sources = (List.range (e - p)).map (p + ·) := by
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  next => simp at h
  next hn => exact ⟨p, e, hp, he, hn, (Option.some.inj h).symm⟩

theorem copiedRow_coreValid_shift {a : Pattern} {last row copied : Row} {source p : Nat}
    (hv : last.CoreValid a.length) (hr : row.CoreValid source)
    (hp : last.p = some p) (hsp : p ≤ source)
    (h : copiedRow a last source row = some copied) :
    copied.CoreValid (source + (a.length - p)) := by
  obtain ⟨owner, ho, hc⟩ := copiedRow_coreValid hv hr h
  have he := copyEntry_high_value hv hp hsp ho
  simpa only [he] using hc

theorem MapsEntries.at {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : MapsEntries f xs ys) {i : Nat} {y : β} (hy : ys[i]? = some y) :
    ∃ x, xs[i]? = some x ∧ f x = some y := by
  induction h generalizing i with
  | nil => simp at hy
  | @cons x z xs ys hx ht ih =>
    cases i with
    | zero =>
      have he : z = y := by simpa using hy
      subst y
      exact ⟨x, rfl, hx⟩
    | succ i =>
      obtain ⟨w, hw, hf⟩ := ih (by simpa using hy)
      exact ⟨w, by simpa using hw, hf⟩

theorem copied_block_coreValid {a : Pattern} {last : Row} {sources : List Nat} {copied : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (hv : last.CoreValid a.length) (hs : shortCopySources last = some sources)
    (h : sources.mapM (fun source => do
      let row ← rowAt a source
      copiedRow a last source row) = some copied) : BlockCoreValid a.length copied := by
  obtain ⟨p, e, hp, _, _, hsrc⟩ := shortCopySources_description hs
  have hpn := fromRight_le_last hv.1 hv.2.2.1 (by omega : 0 < last.step + 1) hp
  intro i hi
  have hget : copied[i]? = some copied[i] := by simp [hi]
  obtain ⟨source, hsource, hrow⟩ := (option_mapM_forall2 h).at hget
  have hsource' := hsource
  rw [hsrc] at hsource'
  obtain ⟨hb, hval⟩ := List.getElem?_eq_some_iff.mp hsource'
  have heq : p + i = source := by simpa using hval
  obtain ⟨row, hr, hc⟩ := Option.bind_eq_some_iff.mp hrow
  have hvalid := copiedRow_coreValid_shift hv (valid source row hr) hp (by omega) hc
  have hiEq : source + (a.length - p) = a.length + i := by omega
  simpa only [hiEq] using hvalid

theorem shortCopy_preserves_coreValid {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (h : shortCopy a = some b) : ∀ r row, rowAt b r = some row → row.CoreValid r := by
  unfold shortCopy at h
  split at h
  next => simp at h
  next hlen =>
    obtain ⟨last, hl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨sources, hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨copied, hc, h⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj h
    have hr : rowAt a a.length = some last := by
      simpa [rowAt, show a.length ≠ 0 by omega, List.getLast?_eq_getElem?] using hl
    have hb := copied_block_coreValid valid (valid a.length last hr) hs hc
    apply coreValid_iff_block.mpr
    apply blockCoreValid_append
    · simpa [List.dropLast_eq_take] using blockCoreValid_take (coreValid_iff_block.mp valid) (a.length - 1)
    · have he : 1 + a.dropLast.length = a.length := by simp; omega
      simpa only [he] using hb

end FullMarkedBLP


