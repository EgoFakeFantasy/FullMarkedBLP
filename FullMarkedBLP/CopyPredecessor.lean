import FullMarkedBLP.CopyIndex

namespace FullMarkedBLP

theorem MapsEntries.at_left {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : MapsEntries f xs ys) {i : Nat} {x : α} (hx : xs[i]? = some x) :
    ∃ y, ys[i]? = some y ∧ f x = some y := by
  induction h generalizing i with
  | nil => simp at hx
  | @cons u v us vs hu ht ih =>
    cases i with
    | zero =>
      have he : u = x := by simpa using hx
      subst x
      exact ⟨v, rfl, hu⟩
    | succ i =>
      obtain ⟨y, hy, hf⟩ := ih (by simpa using hx)
      exact ⟨y, by simpa using hy, hf⟩

theorem MapsEntries.fromRight {f : Nat → Option Nat} {xs ys : List Nat}
    (h : MapsEntries f xs ys) {k x : Nat} (hx : fromRight xs k = some x) :
    ∃ y, fromRight ys k = some y ∧ f x = some y := by
  unfold FullMarkedBLP.fromRight at hx
  split at hx
  next hk =>
    obtain ⟨y, hy, hf⟩ := h.at_left hx
    refine ⟨y, ?_, hf⟩
    simpa [FullMarkedBLP.fromRight, ← h.length_eq, hk] using hy
  next => simp at hx

theorem copiedRow_p {a : Pattern} {last row copied : Row} {source p : Nat}
    (hp : row.p = some p) (h : copiedRow a last source row = some copied) :
    ∃ q, copied.p = some q ∧ copyEntry a.length last p = some q := by
  obtain ⟨core, hc, h⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj h
  exact (copiedCore_maps_entries hc).fromRight hp

theorem shortCopy_copied_rowAt {a b : Pattern} {last : Row} {p e source : Nat}
    (h : shortCopy a = some b) (hl : a.getLast? = some last)
    (hp : last.p = some p) (he : last.e = some e)
    (hps : p ≤ source) (hse : source < e) (hpn : p ≤ a.length) :
    ∃ row copied, rowAt a source = some row ∧ copiedRow a last source row = some copied ∧
      rowAt b (source + (a.length - p)) = some copied := by
  unfold shortCopy at h
  split at h
  next => simp at h
  next hn =>
    obtain ⟨last', hl', h⟩ := Option.bind_eq_some_iff.mp h
    have hh := Option.some.inj (hl'.symm.trans hl)
    subst last'
    obtain ⟨sources, hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨copied, hc, h⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj h
    obtain ⟨p', e', hp', he', _, hsrc⟩ := shortCopySources_description hs
    have hpp := Option.some.inj (hp'.symm.trans hp)
    have hee := Option.some.inj (he'.symm.trans he)
    subst p'; subst e'
    have hidx : source - p < e - p := by omega
    have hsource : sources[source - p]? = some source := by
      rw [hsrc]
      simp [hidx, show p + (source - p) = source by omega]
    obtain ⟨out, hout, hrow⟩ := (option_mapM_forall2 hc).at_left hsource
    obtain ⟨row, hr, hcopy⟩ := Option.bind_eq_some_iff.mp hrow
    refine ⟨row, out, hr, hcopy, ?_⟩
    have hlen : a.dropLast.length = a.length - 1 := by simp
    have hnonzero : source + (a.length - p) ≠ 0 := by omega
    have hge : a.dropLast.length ≤ source + (a.length - p) - 1 := by omega
    have hindex : source + (a.length - p) - 1 - a.dropLast.length = source - p := by omega
    simpa only [rowAt, hnonzero, ↓reduceIte, List.getElem?_append_right hge, hindex] using hout

theorem shortCopy_predecessor {a b : Pattern} {last : Row} {p e source z : Nat}
    (h : shortCopy a = some b) (hl : a.getLast? = some last)
    (hp : last.p = some p) (he : last.e = some e)
    (hps : p ≤ source) (hse : source < e) (hpn : p ≤ a.length)
    (hz : predecessor a source = some z) :
    ∃ q, copyEntry a.length last z = some q ∧
      predecessor b (source + (a.length - p)) = some q := by
  obtain ⟨row, copied, hr, hc, hb⟩ := shortCopy_copied_rowAt h hl hp he hps hse hpn
  have hpz : row.p = some z := by simpa [predecessor, hr] using hz
  obtain ⟨q, hq, hmap⟩ := copiedRow_p hpz hc
  exact ⟨q, hmap, by simp [predecessor, hb, hq]⟩

end FullMarkedBLP



