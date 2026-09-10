import FullMarkedBLP.NativeTargetSourceRank
import FullMarkedBLP.NativeBottomSat
import FullMarkedBLP.NativeSourceTrace

namespace FullMarkedBLP

/-- An entered consecutive B segment above the owner's p value gives literal
parallel p edges in the native output, at the same positive offsets. -/
theorem native_target_segment_predecessor {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r base top k : Nat} {sources : List Nat}
    (hn : native a r = some (b, sources))
    (hp : predecessor a r = some base)
    (entered : base + top ∈ sources)
    (chain : ∀ j, 0 < j → j ≤ top →
      (rowAt a (base + j)).bind Row.b = some (base + j - 1))
    (hk : 0 < k) (hkt : k ≤ top) :
    predecessor b (r + k) = some (base + k) := by
  have hs : nativeSources a r = some sources := by
    obtain ⟨row, hr, hh⟩ := Option.bind_eq_some_iff.mp hn
    obtain ⟨ss, hs, hh⟩ := Option.bind_eq_some_iff.mp hh
    obtain ⟨block, hb, hh⟩ := Option.bind_eq_some_iff.mp hh
    change some (_, ss) = some (b, sources) at hh
    have he := congrArg Prod.snd (Option.some.inj hh)
    dsimp only at he
    simpa only [he] using hs
  obtain ⟨row, hr, hrowp⟩ := Option.bind_eq_some_iff.mp hp
  have hv := valid r row hr
  have hl := Row.step_lt_length hv.2.2.2
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step)
    hv.2.2.2.1 (by omega)
  have hne : sources ≠ [] := by intro hh; simp [hh] at entered
  have walk := nativeSources_nonempty_fuel hr hrowp he hs hne
  have member := nativeSourcesFuel_contains_target_segment walk (Nat.le_refl _) entered chain k hk hkt
  have rank := nativeSourcesFuel_target_segment_rank walk entered chain hk hkt
  have edge := native_source_predecessor valid hn member
  rw [rank] at edge
  have heq : k - 1 + 1 = k := by omega
  simpa only [heq] using edge

theorem native_target_segment_trace {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r base top k : Nat} {sources : List Nat}
    (hn : native a r = some (b, sources))
    (hp : predecessor a r = some base)
    (entered : base + top ∈ sources)
    (chain : ∀ j, 0 < j → j ≤ top →
      (rowAt a (base + j)).bind Row.b = some (base + j - 1))
    (hk : 0 < k) (hkt : k ≤ top) :
    Trace b (base + k) (r + k) [r + k, base + k] := by
  have edge := native_target_segment_predecessor valid hn hp entered chain hk hkt
  exact Trace.next (predecessor_lt (native_preserves_coreValid valid hn) edge) edge Trace.stop

end FullMarkedBLP

