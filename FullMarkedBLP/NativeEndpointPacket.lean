import FullMarkedBLP.NativeTargetEntry
import FullMarkedBLP.NativeTargetParallelEdge

namespace FullMarkedBLP

theorem nativeSources_eligible_fuel {a : Pattern} {r p e : Nat} {row : Row}
    {sources : List Nat} (hr : rowAt a r = some row)
    (eligible : row.core.length ≤ 2 * row.step)
    (hp : row.p = some p) (he : row.e = some e)
    (hs : nativeSources a r = some sources) :
    nativeSourcesFuel a p (e + 1) e = some sources := by
  unfold nativeSources at hs
  rw [hr] at hs
  dsimp only [Bind.bind, Option.bind] at hs
  rw [if_neg (by omega)] at hs
  rw [hp] at hs
  dsimp only [Bind.bind, Option.bind] at hs
  rw [he] at hs
  exact hs

/-- The whole parallel segment follows from the owner's actual p/e endpoints
and the consecutive B geometry, including its exact block size. -/
theorem native_endpoint_parallel_packet {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r base top : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (eligible : row.core.length ≤ 2 * row.step)
    (hp : row.p = some base) (he : row.e = some (base + top + 1))
    (hn : native a r = some (b, sources))
    (chain : ∀ j, 0 < j → j ≤ top + 1 →
      (rowAt a (base + j)).bind Row.b = some (base + j - 1)) :
    sources.length = top ∧ ∀ k, 0 < k → k ≤ top →
      predecessor b (r + k) = some (base + k) ∧
      Trace b (base + k) (r + k) [r + k, base + k] := by
  have walk := nativeSources_eligible_fuel hr eligible hp he (native_sources_of_success hn)
  refine ⟨nativeSourcesFuel_target_segment_exact_length valid walk chain, ?_⟩
  intro k hk hkt
  have hb : (rowAt a (base + top + 1)).bind Row.b = some (base + top) := by
    have hh := chain (top + 1) (by omega) (Nat.le_refl _)
    simpa only [Nat.add_assoc, Nat.add_sub_cancel] using hh
  have entered := nativeSourcesFuel_target_entry walk hb (by omega)
  have hp' : predecessor a r = some base := by simp [predecessor, hr, hp]
  have segment := fun j hj (hjt : j ≤ top) => chain j hj (by omega)
  exact ⟨native_target_segment_predecessor valid hn hp' entered segment hk hkt,
    native_target_segment_trace valid hn hp' entered segment hk hkt⟩

end FullMarkedBLP


