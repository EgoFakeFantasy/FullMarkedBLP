import FullMarkedBLP.NativeTopSat

namespace FullMarkedBLP

/-- Each descent moves the old predecessor into the new e position. -/
theorem nativeLower_e_old_p {row lower : Row} {owner p : Nat} {medium : Bool}
    (hv : row.CoreValid owner) (hstep : 1 < row.step) (hp : row.p = some p)
    (h : nativeLower row owner medium = some lower) : lower.e = some p := by
  have hroom := Row.step_lt_length hv.2.2.2
  have hi : row.core[row.core.length - (row.step + 1)]? = some p := by
    simpa [Row.p, fromRight, show row.step + 1 ≤ row.core.length by omega] using hp
  have hent := nativeLower_keeps_low_entry hv (by omega) hi h
  cases medium with
  | false =>
    have hlen := nativeLower_length hv hstep h
    have hs := nativeLower_step h
    simp only [Bool.false_eq_true, ↓reduceIte] at hs
    have hidx : row.core.length - 2 - (row.step - 1) = row.core.length - (row.step + 1) := by omega
    simpa [Row.e, fromRight, hlen, hs, hidx, show 0 < row.step - 1 by omega,
      show row.step - 1 ≤ row.core.length - 2 by omega] using hent
  | true =>
    have hm := List.mem_of_getLast? hv.2.2.1
    cases Option.some.inj h
    have hidx : row.core.length - 1 - row.step = row.core.length - (row.step + 1) := by omega
    simpa [Row.e, fromRight, List.length_erase_of_mem hm, hidx,
      show 0 < row.step by omega, show row.step ≤ row.core.length - 1 by omega] using hent

theorem nativeSourcesFuel_cons_step {a : Pattern} {p fuel u head : Nat} {tail : List Nat}
    (h : nativeSourcesFuel a p (fuel + 1) u = some (head :: tail)) :
    ∃ row, rowAt a u = some row ∧ row.b = some head ∧ p < head ∧
      nativeSourcesFuel a p fuel head = some tail := by
  unfold nativeSourcesFuel at h
  obtain ⟨row, hr, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨next, hb, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  next hlt =>
    obtain ⟨rest, hrest, hout⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨heq, heqt⟩ := List.cons.inj (Option.some.inj hout)
    subst next; subst rest
    exact ⟨row, hr, hb, hlt, hrest⟩
  next => simp at h

theorem nativeSourcesFuel_nil_stop {a : Pattern} {p fuel u : Nat}
    (h : nativeSourcesFuel a p fuel u = some []) :
    ∃ row v, rowAt a u = some row ∧ row.b = some v ∧ v ≤ p := by
  cases fuel with
  | zero => simp [nativeSourcesFuel] at h
  | succ fuel =>
    unfold nativeSourcesFuel at h
    obtain ⟨row, hr, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hb, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    next =>
      obtain ⟨rest, _, hout⟩ := Option.bind_eq_some_iff.mp h
      simp at hout
    next hle => exact ⟨row, v, hr, hb, by omega⟩

/-- The algorithm supplies every adjacent b edge of its entire source chain. -/
theorem nativeSourcesFuel_chain_edges {a : Pattern} {p fuel u : Nat} {sources : List Nat}
    (h : nativeSourcesFuel a p fuel u = some sources) :
    ∀ x y, (x, y) ∈ (u :: sources).zip sources → ∃ row, rowAt a x = some row ∧ row.b = some y := by
  induction fuel generalizing u sources with
  | zero => simp [nativeSourcesFuel] at h
  | succ fuel ih =>
    cases sources with
    | nil => simp
    | cons head tail =>
      obtain ⟨row, hr, hb, _, ht⟩ := nativeSourcesFuel_cons_step h
      intro x y hm
      simp only [List.zip_cons_cons, List.mem_cons] at hm
      rcases hm with heq | hm
      · obtain ⟨hx, hy⟩ := Prod.mk.inj heq
        subst x; subst y
        exact ⟨row, hr, hb⟩
      · exact ih ht x y hm

end FullMarkedBLP

