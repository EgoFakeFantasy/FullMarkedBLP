import FullMarkedBLP.Sat

namespace FullMarkedBLP

theorem sorted_findIdx {xs : List Nat} (hs : xs.Pairwise (· < ·))
    {k y : Nat} (hk : xs[k]? = some y) : xs.findIdx? (· == y) = some k := by
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hk
  apply List.findIdx?_eq_some_iff_getElem.mpr
  refine ⟨hi, by simpa using he, ?_⟩
  intro j hj
  have hh := List.pairwise_iff_getElem.mp hs j k (by omega) hi hj
  rw [he] at hh
  simpa using Nat.ne_of_lt hh

theorem computeMarkTrace_sound {a : Pattern} {r y : Nat} {row : Row} {xs : List Nat}
    (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (hc : computeMarkTrace a r y = some xs) : MarkTrace a r y xs := by
  unfold computeMarkTrace at hc
  rw [hr] at hc
  dsimp only [Bind.bind, Option.bind] at hc
  obtain ⟨k, hk, hc⟩ := Option.bind_eq_some_iff.mp hc
  split at hc
  next => simp at hc
  next hle =>
    obtain ⟨s, hs, hc⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨hi, he, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hk
    refine ⟨row, k, s, hr, hm, by omega, ?_, hs, traceFuel_sound hc⟩
    apply List.getElem?_eq_some_iff.mpr
    exact ⟨hi, by simpa using he⟩

theorem computeMarkTrace_complete {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r y : Nat} {xs : List Nat} (h : MarkTrace a r y xs) :
    computeMarkTrace a r y = some xs := by
  obtain ⟨row, k, s, hr, _, hle, hk, hs, ht⟩ := h
  have hf := sorted_findIdx (valid r row hr).1 hk
  have hc := (computeTrace_iff valid).mpr ht
  simp [computeMarkTrace, hr, hf, Nat.not_lt.mpr hle, hs, hc]

end FullMarkedBLP
