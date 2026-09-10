import FullMarkedBLP.NativeSatClosure

namespace FullMarkedBLP

theorem nativeSources_empty_local_sat {a : Pattern} {r : Nat} {row : Row}
    (hv : row.CoreValid r) (hr : rowAt a r = some row)
    (heligible : row.core.length ≤ 2 * row.step)
    (h : nativeSources a r = some []) :
    ∃ p e er v, row.p = some p ∧ row.e = some e ∧ rowAt a e = some er ∧ er.b = some v ∧ v ≤ p := by
  have hroom := Row.step_lt_length hv.2.2.2
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.core) (k := row.step + 1) (by omega) (by omega)
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) hv.2.2.2.1 (by omega)
  change row.p = some p at hp
  change row.e = some e at he
  have hf : nativeSourcesFuel a p (e + 1) e = some [] := by
    unfold nativeSources at h
    rw [hr] at h
    dsimp only [Bind.bind, Option.bind] at h
    rw [if_neg (by omega), hp] at h
    dsimp only [Bind.bind, Option.bind] at h
    rw [he] at h
    exact h
  obtain ⟨er, v, her, hb, hle⟩ := nativeSourcesFuel_nil_stop hf
  exact ⟨p, e, er, v, hp, he, her, hb, hle⟩

/-- Native establishes Sat at its owner while preserving it everywhere else. -/
theorem native_sat_of_others {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {sources : List Nat}
    (hs : ∀ i row, i ≠ r → rowAt a i = some row → row.core.length ≤ 2 * row.step →
      ∃ p e er v, row.p = some p ∧ row.e = some e ∧ rowAt a e = some er ∧ er.b = some v ∧ v ≤ p)
    (hn : native a r = some (b, sources)) : Sat b := by
  by_cases hne : sources = []
  · subst sources
    obtain ⟨old, hold, _⟩ := Option.bind_eq_some_iff.mp hn
    have hsrc := native_sources_of_success hn
    have hidentity := native_empty hold hsrc
    have heq := (Prod.mk.inj (Option.some.inj (hn.symm.trans hidentity))).1
    subst b
    intro i row hi heligible
    by_cases hir : i = r
    · subst i
      exact nativeSources_empty_local_sat (valid r row hi) hi heligible hsrc
    · exact hs i row hir hi heligible
  · exact native_sat_nonempty_of_others valid hs hn hne

end FullMarkedBLP


