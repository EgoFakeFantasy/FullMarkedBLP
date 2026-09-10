import FullMarkedBLP.CopyTraceSplice

namespace FullMarkedBLP

theorem copyPositionGuard_source_lt {core : List Nat} {step idx minimum s : Nat}
    (hc : core.Pairwise (· < ·)) (hi : step ≤ idx)
    (hs : core[idx - step]? = some s)
    (hg : copyPositionGuard core step idx minimum = true) : s < minimum := by
  have hle : step ≤ idx + 1 := by omega
  simp only [copyPositionGuard, hle, ↓reduceIte] at hg
  cases hn : core[idx + 1 - step]? with
  | none => simp [hn] at hg
  | some next =>
    have hnext : next ≤ minimum := by simpa [hn] using hg
    obtain ⟨hb, he⟩ := List.getElem?_eq_some_iff.mp hs
    obtain ⟨hb', he'⟩ := List.getElem?_eq_some_iff.mp hn
    have hlt := List.pairwise_iff_getElem.mp hc (idx - step) (idx + 1 - step) hb hb' (by omega)
    omega

theorem trace_tail_at_member {a : Pattern} {s y low : Nat} {xs : List Nat}
    (ht : Trace a s y xs) (hm : low ∈ xs) : ∃ tail, Trace a s low tail := by
  induction ht with
  | stop =>
    have hh : low = s := by simpa using hm
    subst low
    exact ⟨[s], Trace.stop⟩
  | @next y z rest hsy hp hr ih =>
    rcases List.mem_cons.mp hm with he | hm
    · subst low; exact ⟨y :: rest, Trace.next hsy hp hr⟩
    · exact ih hm

/-- Recover the source of a marked trace from its exact step pair. -/
theorem row_trace_at_pair {a : Pattern} {row : Row} {owner k low shifted : Nat}
    (hv : row.CoreValid owner) (ht : row.HasTraces a)
    (hm : shifted ∈ row.marks)
    (hlo : row.core[k]? = some low)
    (hsh : row.core[k + row.step]? = some shifted) :
    ∃ word, Trace a low shifted word := by
  obtain ⟨j, s, word, _, hj, hs, htrace⟩ := ht shifted hm
  have he : j = k + row.step := Option.some.inj ((sorted_findIdx hv.1 hj).symm.trans
    (sorted_findIdx hv.1 hsh))
  subst j
  have hs' : row.core[k]? = some s := by simpa using hs
  have heq := Option.some.inj (hs'.symm.trans hlo)
  subst s
  exact ⟨word, htrace⟩

/-- The old last-row marked trace joins to the original low tail inside the unchanged prefix. -/
theorem shortCopy_middle_bridge {a b : Pattern} {last : Row}
    {s y low shifted p k : Nat} {xs : List Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (h : shortCopy a = some b) (hv : last.CoreValid a.length)
    (hm : last.ProperMarks a.length) (htraces : last.HasTraces a)
    (hmark : shifted ∈ last.marks) (hlo : last.core[k]? = some low)
    (hshift : last.core[k + last.step]? = some shifted)
    (ht : Trace a s y xs) (hf : xs.find? (· < p) = some low)
    (hpn : p ≤ a.length) : ∃ bridge, Trace b s shifted bridge := by
  obtain ⟨front, hfront⟩ := row_trace_at_pair hv htraces hmark hlo hshift
  obtain ⟨tail, htail⟩ := trace_tail_at_member ht (List.mem_of_find?_eq_some hf)
  have hlow : low < p := by simpa using List.find?_some hf
  have hshifted := (hm.2 shifted hmark).1
  have hfront' := shortCopy_prefix_trace valid h hfront hshifted
  have htail' := shortCopy_prefix_trace valid h htail (by omega)
  exact ⟨front.dropLast ++ tail, trace_join hfront' htail'⟩

theorem copyEntry_middle_pair {row : Row} {n minimum p e k low shifted : Nat}
    (hv : row.CoreValid n) (hm : row.core.head? = some minimum)
    (hp : row.p = some p) (he : row.e = some e) (hpn : p ≠ 0)
    (hmin : minimum ≤ low) (hlp : low < p) (hle : low ≤ e)
    (hlo : row.core[k]? = some low) (hsh : row.core[k + row.step]? = some shifted) :
    copyEntry n row low = some shifted := by
  have hdrop : (row.core.drop row.step)[k]? = some shifted := by
    simpa [Nat.add_comm] using hsh
  have hpair : (low, shifted) ∈ row.core.zip (row.core.drop row.step) := by
    apply List.mem_of_getElem? (i := k)
    exact List.getElem?_zip_eq_some.mpr ⟨hlo, hdrop⟩
  cases hf : (row.core.zip (row.core.drop row.step)).find? (fun pair => pair.1 == low) with
  | none =>
    have hh := List.find?_eq_none.mp hf (low, shifted) hpair
    simp at hh
  | some pair =>
    have hmap : ((row.core.zip (row.core.drop row.step)).find? (fun pair => pair.1 == low)).map Prod.snd = some pair.2 := by simp [hf]
    obtain ⟨j, hj, hjsh⟩ := copy_pair_lookup hmap
    have hjk := Option.some.inj ((sorted_findIdx hv.1 hj).symm.trans (sorted_findIdx hv.1 hlo))
    subst j
    have hvv := Option.some.inj (hjsh.symm.trans hsh)
    simp [copyEntry, hm, hp, he, hpn, show ¬e < low by omega,
      show ¬low < minimum by omega, show ¬p ≤ low by omega, hf, hvv]

theorem shortCopy_middle_trace {a b : Pattern} {last : Row}
    {p e minimum low shifted k s y s' y' : Nat} {xs : List Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (h : shortCopy a = some b) (hl : a.getLast? = some last)
    (hp : last.p = some p) (he : last.e = some e)
    (hm : last.core.head? = some minimum) (hmin : minimum ≤ low)
    (hle : low ≤ e) (hye : y < e) (hpn : p ≤ a.length)
    (hv : last.CoreValid a.length) (hmarks : last.ProperMarks a.length)
    (htraces : last.HasTraces a) (hmark : shifted ∈ last.marks)
    (hlo : last.core[k]? = some low) (hshift : last.core[k + last.step]? = some shifted)
    (ht : Trace a s y xs) (hf : xs.find? (· < p) = some low)
    (hs : copyEntry a.length last s = some s') (hsmin : s' < minimum)
    (hy : copyEntry a.length last y = some y') : ∃ word, Trace b s' y' word := by
  have hslow := copyEntry_not_below_input hv hs
  have hss := copyEntry_low_value hm (by omega : s < minimum) hs
  have hlp : low < p := by simpa using List.find?_some hf
  have hmap := copyEntry_middle_pair hv hm hp he (by omega) hmin hlp hle hlo hshift
  obtain ⟨bridge, hb⟩ := shortCopy_middle_bridge valid h hv hmarks htraces hmark hlo hshift ht hf hpn
  have hb' : Trace b s' shifted bridge := by simpa only [hss] using hb
  exact shortCopy_trace_splice valid h hl hp he hye hpn hv ht hf hs hy hmap hb'

end FullMarkedBLP




