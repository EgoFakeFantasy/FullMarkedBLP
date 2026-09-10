import FullMarkedBLP.PacketAllEndpoints

namespace FullMarkedBLP

/-- Guarded internal factors have empty current native sources. Their packet
information must therefore be recovered from recorded births, not recomputed. -/
theorem currentPlusOne_internal_native_empty {a : Pattern}
    (valid : ∀ i row, rowAt a i = some row → row.CoreValid i)
    {s y : Nat} {xs : List Nat} (trace : Trace a s y xs)
    (guard : currentPlusOne a xs = true) :
    ∀ parent child, (parent, child) ∈ xs.dropLast.zip xs.dropLast.tail →
      nativeSources a parent = some [] ∧ native a parent = some (a, []) := by
  intro parent child pair
  obtain ⟨row, hr, hp, he⟩ := currentPlusOne_all_endpoints valid trace guard parent child pair
  obtain ⟨endpoint, v, endpointAt, hb, bound⟩ := currentPlusOne_all_endpoint_b_bounds valid trace guard parent child pair
  have empty : nativeSources a parent = some [] := by
    by_cases long : 2 * row.step < row.core.length
    · simp [nativeSources, hr, long]
    · simp [nativeSources, hr, long, hp, he, nativeSourcesFuel, endpointAt, hb, Nat.not_lt.mpr bound]
  exact ⟨empty, native_empty hr empty⟩

end FullMarkedBLP
