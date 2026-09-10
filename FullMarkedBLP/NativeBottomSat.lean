import FullMarkedBLP.NativeBlockEndpoint

namespace FullMarkedBLP

theorem nativeSources_nonempty_fuel {a : Pattern} {r p e : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (h : nativeSources a r = some sources) (hne : sources ≠ []) :
    nativeSourcesFuel a p (e + 1) e = some sources := by
  unfold nativeSources at h
  rw [hr] at h
  dsimp only [Bind.bind, Option.bind] at h
  split at h
  next =>
    have hh : sources = [] := (Option.some.inj h).symm
    exact False.elim (hne hh)
  next =>
    rw [hp] at h
    dsimp only [Bind.bind, Option.bind] at h
    rw [he] at h
    exact h

theorem nativeSourcesFuel_last_stop {a : Pattern} {p fuel u last : Nat} {sources : List Nat}
    (h : nativeSourcesFuel a p fuel u = some sources) (hl : sources.getLast? = some last) :
    ∃ row v, rowAt a last = some row ∧ row.b = some v ∧ v ≤ p := by
  induction fuel generalizing u sources with
  | zero => simp [nativeSourcesFuel] at h
  | succ fuel ih =>
    cases sources with
    | nil => simp at hl
    | cons head tail =>
      obtain ⟨_, _, _, _, ht⟩ := nativeSourcesFuel_cons_step h
      cases tail with
      | nil =>
        have he : head = last := by simpa using hl
        subst last
        exact nativeSourcesFuel_nil_stop ht
      | cons next rest =>
        exact ih ht (by simpa using hl)

theorem decreasing_last_min {xs : List Nat} {last : Nat}
    (hs : xs.Pairwise (· > ·)) (hl : xs.getLast? = some last) :
    ∀ x ∈ xs, last ≤ x := by
  induction xs with
  | nil => simp at hl
  | cons head tail ih =>
    cases tail with
    | nil =>
      have he : head = last := by simpa using hl
      simp [he]
    | cons next rest =>
      have hl' : (next :: rest).getLast? = some last := by simpa using hl
      have hp := List.pairwise_cons.mp hs
      intro x hx
      rcases List.mem_cons.mp hx with he | hx
      · subst x
        have hh := hp.1 last (List.mem_of_getLast? hl')
        omega
      · exact ih hp.2 hl' x hx

theorem native_bottom_sat_witness {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p e last : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hsrc : nativeSources a r = some sources) (hlast : sources.getLast? = some last)
    (hn : native a r = some (b, sources)) :
    ∃ bottom er v, rowAt b r = some bottom ∧ bottom.p = some p ∧ bottom.e = some last ∧
      rowAt b last = some er ∧ er.b = some v ∧ v ≤ p := by
  have hx := List.mem_of_getLast? hlast
  have hne : sources ≠ [] := by intro hh; simp [hh] at hlast
  obtain ⟨er, v, her, hb, hv⟩ := nativeSourcesFuel_last_stop
    (nativeSources_nonempty_fuel hr hp he hsrc hne) hlast
  have hmin := decreasing_last_min (nativeSources_decreasing valid hsrc) hlast
  have hf : sources.filter (· < last) = [] := List.filter_eq_nil_iff.mpr
    (fun x hx => by have hh := hmin x hx; simp; omega)
  have hlow := nativeSources_below_owner valid hr hsrc last hx
  have her' := (native_prefix_rowAt hn hlow).trans her
  have hout := hn
  unfold native at hout
  rw [hr] at hout
  dsimp only [Bind.bind, Option.bind] at hout
  rw [hsrc] at hout
  dsimp only [Bind.bind, Option.bind] at hout
  obtain ⟨block, hblock, hout⟩ := Option.bind_eq_some_iff.mp hout
  have hpattern := (Prod.mk.inj (Option.some.inj hout)).1
  have hlen := nativeBlock_length hblock
  have hi : 0 < block.length := by omega
  have hbp := nativeBlock_bottom_p valid hr hp hsrc hblock
  have hbe := nativeBlock_source_e valid hr hp he hsrc hx hblock
  simp only [hf, List.length_nil] at hbe
  have hpbot : (block[0]).p = some p := by
    simpa [List.head?_eq_getElem?, List.getElem?_eq_getElem hi] using hbp
  have hebot : (block[0]).e = some last := by
    simpa only [List.getElem?_eq_getElem hi, Option.bind_some] using hbe
  have hrow := native_block_rowAt (sources := sources) hr hi
  have hrow' : rowAt b r = some block[0] := by
    simpa only [hpattern, Nat.add_zero, List.getElem?_eq_getElem hi] using hrow
  exact ⟨block[0], er, v, hrow', hpbot, hebot, her', hb, hv⟩

end FullMarkedBLP

