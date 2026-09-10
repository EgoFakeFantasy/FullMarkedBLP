import FullMarkedBLP.NativeActualTargetBChain

namespace FullMarkedBLP

/-- The consecutive target B chain is present in the actual native output. -/
theorem native_output_target_b {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r k : Nat} {sources : List Nat} (hn : native a r = some (b, sources))
    (hk : 0 < k) (hkt : k ≤ sources.length) :
    (rowAt b (r + k)).bind Row.b = some (r + k - 1) := by
  obtain ⟨row, hr, hn⟩ := Option.bind_eq_some_iff.mp hn
  obtain ⟨ss, hs, hn⟩ := Option.bind_eq_some_iff.mp hn
  obtain ⟨block, hb, hn⟩ := Option.bind_eq_some_iff.mp hn
  change some (_, ss) = some (b, sources) at hn
  cases Option.some.inj hn
  have hlen := nativeBlock_length hb
  have hi : k < block.length := by omega
  have hne : sources ≠ [] := by intro h; simp [h] at hkt; omega
  have hvalue := nativeBlock_actual_target_b valid hr hs hne hb k hi hk
  rw [native_block_rowAt (sources := sources) hr hi]
  simp only [List.getElem?_eq_getElem hi, Option.bind_some, hvalue]

end FullMarkedBLP
