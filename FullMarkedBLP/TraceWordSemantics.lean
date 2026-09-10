import FullMarkedBLP.WeakAgreementEdges

namespace FullMarkedBLP

theorem realized_trace_word_image {α : Type u} {a : Pattern}
    (action : Nat → α → α) (theta : Nat → α)
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (edges : ∀ r row, rowAt a r = some row → row.RealizesEdges (action r) theta r)
    {s y : Nat} {xs : List Nat} (ht : Trace a s y xs) :
    evalWord action xs.dropLast (theta s) = theta y := by
  induction ht with
  | stop => rfl
  | @next y z tail hsy hp ht ih =>
    obtain ⟨row, hr, hrp⟩ := Option.bind_eq_some_iff.mp hp
    have he := realizesEdges_p (valid y row hr) (edges y row hr) hrp
    cases tail with
    | nil => exact False.elim (trace_nonempty ht rfl)
    | cons v rest => simpa only [List.dropLast_cons_cons, evalWord, ih] using he

theorem evalWord_ordinal_action {V : Type u} {O : Type v}
    (embedding : Nat → V → V) (action : Nat → O → O) (ord : O → V)
    (compat : ∀ i x, embedding i (ord x) = ord (action i x))
    (word : List Nat) (x : O) :
    evalWord embedding word (ord x) = ord (evalWord action word x) := by
  induction word with
  | nil => rfl
  | cons v tail ih => simp only [evalWord, ih, compat]

theorem realized_trace_set_image {V : Type u} {O : Type v} {a : Pattern}
    (embedding : Nat → V → V) (action : Nat → O → O) (ord : O → V) (theta : Nat → O)
    (compat : ∀ i x, embedding i (ord x) = ord (action i x))
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (edges : ∀ r row, rowAt a r = some row → row.RealizesEdges (action r) theta r)
    {s y : Nat} {xs : List Nat} (ht : Trace a s y xs) :
    evalWord embedding xs.dropLast (ord (theta s)) = ord (theta y) := by
  rw [evalWord_ordinal_action embedding action ord compat,
    realized_trace_word_image action theta valid edges ht]

/-- Weak agreement reads the exact marked source edge from its actual word.
    The source and target cutoff bounds are explicit; no pointwise agreement
    or bound on the owner's unknown image is assumed. -/
theorem weak_trace_reads_source_edge {V : Type u} {O : Type v} {a : Pattern}
    (mem : V → V → Prop) (below : O → V → Prop) (ord : O → V)
    (lt : O → O → Prop)
    (irrefl : ∀ x, ¬lt x x) (trans : ∀ {x y z}, lt x y → lt y z → lt x z)
    (compare : ∀ x y, x = y ∨ lt x y ∨ lt y x)
    (ordinalMem : ∀ x y, mem (ord x) (ord y) ↔ lt x y)
    (ordinalBelow : ∀ delta x, lt x delta → below delta (ord x))
    (embedding : Nat → V → V) (action : Nat → O → O) (theta : Nat → O)
    (compat : ∀ i x, embedding i (ord x) = ord (action i x))
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (edges : ∀ r row, rowAt a r = some row → row.RealizesEdges (action r) theta r)
    {s y owner : Nat} {xs : List Nat} {delta : O} (ht : Trace a s y xs)
    (hs : lt (theta s) delta) (hy : lt (theta y) delta)
    (hw : cutoffAgreement mem below delta (embedding owner) (evalWord embedding xs.dropLast)) :
    embedding owner (ord (theta s)) = ord (theta y) := by
  exact cutoffAgreement_reads_edge mem below ord lt irrefl trans compare ordinalMem ordinalBelow
    (cutoffAgreement_symm hw) (ordinalBelow delta (theta s) hs)
    (realized_trace_set_image embedding action ord theta compat valid edges ht)
    ⟨action owner (theta s), compat owner (theta s)⟩ hy

end FullMarkedBLP
