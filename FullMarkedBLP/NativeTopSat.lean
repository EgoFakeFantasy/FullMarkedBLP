import FullMarkedBLP.CompletionSat

namespace FullMarkedBLP

theorem nativeTop_e {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p e : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (h : nativeSources a r = some sources) : (nativeTop row r sources).e = some e := by
  have hv := valid r row hr
  have hstep := hv.2.2.2.1
  have hroom := Row.step_lt_length hv.2.2.2
  have hei : row.core[row.core.length - row.step]? = some e := by
    simpa [Row.e, fromRight, hstep, show row.step ≤ row.core.length by omega] using he
  have her := fromRight_le_last hv.1 hv.2.2.1 hstep he
  have hf : sources.filter (· < e) = sources := List.filter_eq_self.mpr
    (fun x hx => by simpa using (nativeSources_between valid hr hp he h x hx).2)
  have hrank := nativeTop_rank_exact valid hr h her
  rw [hf, sorted_rank_at_index hv.1 hei] at hrank
  have hmem := (nativeTop_core_mem row r sources e).mpr (Or.inl (List.mem_of_getElem? hei))
  have hent := sorted_get_at_rank (nativeTop_sorted row r sources).1 hmem
  rw [hrank] at hent
  have hlen := nativeTop_actual_length valid hr h
  have hst : (nativeTop row r sources).step = row.step + sources.length := rfl
  have hidx : row.core.length + 2 * sources.length - (row.step + sources.length) =
      row.core.length - row.step + sources.length := by omega
  simpa [Row.e, fromRight, hlen, hst, hidx,
    show 0 < row.step + sources.length by omega,
    show row.step + sources.length ≤ row.core.length + 2 * sources.length by omega] using hent

theorem nativeTop_p_head {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p e head : Nat} {row : Row} {tail : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (h : nativeSources a r = some (head :: tail)) : (nativeTop row r (head :: tail)).p = some head := by
  have hv := valid r row hr
  have hroom := Row.step_lt_length hv.2.2.2
  have hdec := List.pairwise_cons.mp (nativeSources_decreasing valid h)
  have hf : (head :: tail).filter (· < head) = tail := by
    have ht : tail.filter (· < head) = tail := List.filter_eq_self.mpr (fun x hx => by simpa using hdec.1 x hx)
    simp [ht]
  have hent := nativeTop_source_entry valid hr hp he h (by simp : head ∈ head :: tail)
  rw [hf] at hent
  have hlen := nativeTop_actual_length valid hr h
  have hst : (nativeTop row r (head :: tail)).step = row.step + (head :: tail).length := rfl
  simp only [List.length_cons] at hlen hst
  have hidx : row.core.length + 2 * (tail.length + 1) - (row.step + (tail.length + 1) + 1) =
      row.core.length - (row.step + 1) + 1 + tail.length := by omega
  simpa [Row.p, fromRight, hlen, hst, hidx,
    show row.step + (tail.length + 1) + 1 ≤ row.core.length + 2 * (tail.length + 1) by omega] using hent

theorem nativeSources_head_b {a : Pattern} {r p e head : Nat} {row : Row} {tail : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (h : nativeSources a r = some (head :: tail)) :
    ∃ er, rowAt a e = some er ∧ er.b = some head := by
  unfold nativeSources at h
  rw [hr] at h
  dsimp only [Bind.bind, Option.bind] at h
  split at h
  next => simp at h
  next =>
    rw [hp] at h
    dsimp only [Bind.bind, Option.bind] at h
    rw [he] at h
    dsimp only [Bind.bind, Option.bind] at h
    unfold nativeSourcesFuel at h
    obtain ⟨er, her, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hb, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    next =>
      obtain ⟨rest, _, hout⟩ := Option.bind_eq_some_iff.mp h
      have hv := (List.cons.inj (Option.some.inj hout)).1
      exact ⟨er, her, by simpa only [hv] using hb⟩
    next => simp at h

theorem native_top_sat_witness {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p e head : Nat} {row : Row} {tail : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hsrc : nativeSources a r = some (head :: tail))
    (hn : native a r = some (b, head :: tail)) :
    (nativeTop row r (head :: tail)).p = some head ∧
    (nativeTop row r (head :: tail)).e = some e ∧
    ∃ er, rowAt b e = some er ∧ er.b = some head := by
  obtain ⟨er, her, hb⟩ := nativeSources_head_b hr hp he hsrc
  have hv := valid r row hr
  have hstep : 1 < row.step := nativeSources_nonempty_step_ge_two hv hr hsrc (by simp)
  have herlt := fromRight_lt_last hv.1 hv.2.2.1 hstep he
  exact ⟨nativeTop_p_head valid hr hp he hsrc, nativeTop_e valid hr hp he hsrc,
    er, (native_prefix_rowAt hn herlt).trans her, hb⟩

end FullMarkedBLP



