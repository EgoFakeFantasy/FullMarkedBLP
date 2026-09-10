import FullMarkedBLP.FrozenEntryTrace

namespace FullMarkedBLP

/-- Successful deterministic B walks agree regardless of their fuel budgets. -/
theorem nativeSourcesFuel_unique {a : Pattern} {p fuel u : Nat} {xs : List Nat}
    (h : nativeSourcesFuel a p fuel u = some xs) :
    ∀ other ys, nativeSourcesFuel a p other u = some ys → xs = ys := by
  induction fuel generalizing u xs with
  | zero => simp [nativeSourcesFuel] at h
  | succ fuel ih =>
    intro other ys hy
    cases other with
    | zero => simp [nativeSourcesFuel] at hy
    | succ other =>
      obtain ⟨row, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
      change row.b = some v at hv
      simp only [nativeSourcesFuel, hr] at hy
      dsimp only [Bind.bind, Option.bind] at hy
      rw [hv] at hy
      dsimp only [Bind.bind, Option.bind] at hy
      split at h
      next hp =>
        obtain ⟨tail, ht, he⟩ := Option.bind_eq_some_iff.mp h
        have hys : ∃ tail', nativeSourcesFuel a p other v = some tail' ∧ v :: tail' = ys := by
          rw [if_pos hp] at hy
          obtain ⟨tail', ht', he'⟩ := Option.bind_eq_some_iff.mp hy
          exact ⟨tail', ht', Option.some.inj he'⟩
        obtain ⟨tail', ht', he'⟩ := hys
        have hh := ih ht other tail' ht'
        have heq : v :: tail = xs := Option.some.inj he
        rw [← heq, ← he', hh]
      next hp =>
        have hx : xs = [] := by simpa using h.symm
        have hy' : ys = [] := by simpa [hp] using hy.symm
        exact hx.trans hy'.symm

/-- Every emitted source starts a strictly shorter successful suffix walk. -/
theorem nativeSourcesFuel_member_suffix {a : Pattern} {p fuel u x : Nat} {xs : List Nat}
    (h : nativeSourcesFuel a p fuel u = some xs) (hx : x ∈ xs) :
    ∃ budget tail, nativeSourcesFuel a p budget x = some tail ∧ tail.length < xs.length := by
  induction fuel generalizing u xs with
  | zero => simp [nativeSourcesFuel] at h
  | succ fuel ih =>
    obtain ⟨row, hr, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    next =>
      obtain ⟨tail, ht, he⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj he
      rcases List.mem_cons.mp hx with hx | hx
      · subst x
        exact ⟨fuel, tail, ht, by simp⟩
      · obtain ⟨budget, suffix, hs, hlen⟩ := ih ht hx
        exact ⟨budget, suffix, hs, by simp; omega⟩
    next =>
      have he : xs = [] := by simpa using h.symm
      simp [he] at hx

theorem nativeSourcesFuel_no_self {a : Pattern} {p fuel u : Nat} {xs : List Nat}
    (h : nativeSourcesFuel a p fuel u = some xs) : u ∉ xs := by
  intro hu
  obtain ⟨budget, tail, ht, hlen⟩ := nativeSourcesFuel_member_suffix h hu
  have he := nativeSourcesFuel_unique h budget tail ht
  subst tail
  omega

theorem nativeSourcesFuel_nodup_of_success {a : Pattern} {p fuel u : Nat} {xs : List Nat}
    (h : nativeSourcesFuel a p fuel u = some xs) : xs.Nodup := by
  induction fuel generalizing u xs with
  | zero => simp [nativeSourcesFuel] at h
  | succ fuel ih =>
    obtain ⟨row, hr, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    next =>
      obtain ⟨tail, ht, he⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj he
      exact List.nodup_cons.mpr ⟨nativeSourcesFuel_no_self ht, ih ht⟩
    next =>
      have he : xs = [] := by simpa using h.symm
      simp [he]

theorem nativeSources_nodup_of_success {a : Pattern} {r : Nat} {sources : List Nat}
    (h : nativeSources a r = some sources) : sources.Nodup := by
  obtain ⟨row, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  next =>
    have he : sources = [] := by simpa using h.symm
    simp [he]
  next =>
    obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e, _, h⟩ := Option.bind_eq_some_iff.mp h
    exact nativeSourcesFuel_nodup_of_success h

theorem scanReach_record_nodup {initial a : Pattern} {rec : Records} {r : Nat}
    (reach : ScanReach initial a rec r) {terminal : Nat} {sources : List Nat}
    (hm : (terminal, sources) ∈ rec) : sources.Nodup := by
  obtain ⟨before, after, history, _, _, hn⟩ := scanReach_record_origin reach hm
  exact nativeSources_nodup_of_success (native_sources_of_success hn)

/-- Even during arbitrary current-owner edits, record lookup cannot return
    duplicate sources; no validity assumption on those edits is needed. -/
theorem completion_record_nodup_of_history {initial a current : Pattern} {rec : Records}
    {r owner y : Nat} {sources : List Nat}
    (reach : ScanReach initial a rec r)
    (hc : completionRecord current rec owner y = some sources) : sources.Nodup := by
  obtain ⟨xs, terminal, _, _, hr, _, _⟩ := completionRecord_iff.mp hc
  exact scanReach_record_nodup reach (recordAt_mem hr)

end FullMarkedBLP




