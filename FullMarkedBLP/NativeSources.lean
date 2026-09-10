import FullMarkedBLP.NativeGeometry

namespace FullMarkedBLP

theorem nativeSourcesFuel_bounds {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {p fuel u : Nat} {sources : List Nat}
    (h : nativeSourcesFuel a p fuel u = some sources) :
    ∀ x ∈ sources, p < x ∧ x < u := by
  induction fuel generalizing u sources with
  | zero => simp [nativeSourcesFuel] at h
  | succ fuel ih =>
    obtain ⟨row, hr, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    next hp =>
      obtain ⟨tail, ht, h⟩ := Option.bind_eq_some_iff.mp h
      change some (b :: tail) = some sources at h
      cases Option.some.inj h
      have hd := native_source_lt valid hr hb
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hp, hd⟩
      · have hi := ih ht x hx
        exact ⟨hi.1, Nat.lt_trans hi.2 hd⟩
    next =>
      change some [] = some sources at h
      cases Option.some.inj h
      simp

theorem nativeSourcesFuel_decreasing {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {p fuel u : Nat} {sources : List Nat}
    (h : nativeSourcesFuel a p fuel u = some sources) :
    sources.Pairwise (· > ·) := by
  induction fuel generalizing u sources with
  | zero => simp [nativeSourcesFuel] at h
  | succ fuel ih =>
    obtain ⟨row, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    next =>
      obtain ⟨tail, ht, h⟩ := Option.bind_eq_some_iff.mp h
      change some (b :: tail) = some sources at h
      cases Option.some.inj h
      exact List.pairwise_cons.mpr
        ⟨fun x hx => (nativeSourcesFuel_bounds valid ht x hx).2, ih ht⟩
    next =>
      change some [] = some sources at h
      cases Option.some.inj h
      exact List.Pairwise.nil

theorem nativeSourcesFuel_nodup {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {p fuel u : Nat} {sources : List Nat}
    (h : nativeSourcesFuel a p fuel u = some sources) : sources.Nodup :=
  (nativeSourcesFuel_decreasing valid h).imp (fun hh => Nat.ne_of_gt hh)

theorem nativeSources_decreasing {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {sources : List Nat} (h : nativeSources a r = some sources) :
    sources.Pairwise (· > ·) := by
  obtain ⟨row, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  next =>
    change some [] = some sources at h
    cases Option.some.inj h
    exact List.Pairwise.nil
  next =>
    obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e, _, h⟩ := Option.bind_eq_some_iff.mp h
    exact nativeSourcesFuel_decreasing valid h


theorem between_adjacent_not_mem {xs : List Nat} (hs : xs.Pairwise (· < ·))
    {i p e x : Nat} (hp : xs[i]? = some p) (he : xs[i + 1]? = some e)
    (hpx : p < x) (hxe : x < e) : x ∉ xs := by
  intro hx
  obtain ⟨hi, hpi⟩ := List.getElem?_eq_some_iff.mp hp
  obtain ⟨hi1, hei⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨j, hj, hxj⟩ := List.mem_iff_getElem.mp hx
  by_cases hji : j < i
  · have hh := List.pairwise_iff_getElem.mp hs j i hj hi hji
    rw [hxj, hpi] at hh
    omega
  · by_cases hjeq : j = i
    · subst j; omega
    · by_cases hjeq1 : j = i + 1
      · subst j; omega
      · have hh := List.pairwise_iff_getElem.mp hs (i + 1) j hi1 hj (by omega)
        rw [hei, hxj] at hh
        omega

theorem nativeSources_disjoint {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (h : nativeSources a r = some sources) :
    ∀ x ∈ sources, x ∉ row.core := by
  unfold nativeSources at h
  rw [hr] at h
  dsimp only [Bind.bind, Option.bind] at h
  split at h
  next =>
    change some [] = some sources at h
    cases Option.some.inj h
    simp
  next =>
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
    have hv := valid r row hr
    have hl := Row.step_lt_length hv.2.2.2
    have hpos := hv.2.2.2.1
    have hpi : row.core[row.core.length - (row.step + 1)]? = some p := by
      simpa [Row.p, fromRight, show row.step + 1 ≤ row.core.length by omega] using hp
    have hei : row.core[row.core.length - (row.step + 1) + 1]? = some e := by
      have hi : row.core.length - (row.step + 1) + 1 = row.core.length - row.step := by omega
      simpa [Row.e, fromRight, hpos, show row.step ≤ row.core.length by omega, hi] using he
    intro x hx
    have hb := nativeSourcesFuel_bounds valid h x hx
    exact between_adjacent_not_mem hv.1 hpi hei hb.1 hb.2

end FullMarkedBLP
