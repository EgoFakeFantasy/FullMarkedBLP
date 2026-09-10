import FullMarkedBLP.RankPointwiseImage

namespace FullMarkedBLP

theorem rankGraph_subset_of_applies {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {f g x y : RankDomain lambda} (between : rankGraphBetween f x y)
    (edges : ∀ a : RankDomain lambda, a.val ∈ x.val → ∀ b : RankDomain lambda,
      rankGraphApplies f a b → rankGraphApplies g a b) : f.val ⊆ g.val := by
  intro p hp
  obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp ((rankGraphBetween_iff hl _ _ _).mp between hp)
  exact (rankGraphApplies_iff hl _ _ _).mp
    (edges (rankMember x a ha) ha (rankMember y b hb) ((rankGraphApplies_iff hl _ _ _).mpr hp))

theorem rankFunction_ext {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {f g x y z : RankDomain lambda} (hf : rankIsFunction f x y) (hg : rankIsFunction g x z)
    (edges : ∀ a : RankDomain lambda, a.val ∈ x.val → ∀ b : RankDomain lambda,
      rankGraphApplies f a b ↔ rankGraphApplies g a b) : f = g := by
  apply Subtype.ext
  apply ZFSet.ext
  intro p
  exact ⟨fun hp => rankGraph_subset_of_applies hl hf.1 (fun a ha b => (edges a ha b).mp) hp,
    fun hp => rankGraph_subset_of_applies hl hg.1 (fun a ha b => (edges a ha b).mpr) hp⟩

/-- A function with a pointwise fixed indexing set and values in the
pointwise image of t is itself the image of a genuine function into t.
This is the countable preimage step of Kunen's contradiction. -/
theorem rankFunction_preimage_of_pointwiseImage {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (j : RankElementaryEmbedding lambda)
    (x t : RankDomain lambda) (fixedDomain : j x = x)
    (fixedMembers : ∀ a : RankDomain lambda, a.val ∈ x.val → j a = a)
    {s : RankDomain lambda} (function : rankIsFunction s x (rankPointwiseImage j t)) :
    ∃ old : RankDomain lambda, rankIsFunction old x t ∧ j old = s := by
  classical
  let values := zfGraphFunction ((rankIsFunction_iff hl _ _ _).mp function)
  have preimages : ∀ a : x.val, ∃ b : t.val,
      (j (rankMember t b.val b.property)).val = (values a).val := by
    intro a
    exact (rankPointwiseImage_mem j t _).mp (values a).property
  choose previous previousSpec using preimages
  let old := rankFunctionGraph hl x t previous
  have oldFunction := rankFunctionGraph_isFunction hl x t previous
  have imageFunction := (rankElementary_function_iff j old x t).mpr oldFunction
  rw [fixedDomain] at imageFunction
  refine ⟨old, oldFunction, ?_⟩
  apply rankFunction_ext hl imageFunction function
  intro a ha b
  let input : x.val := ⟨a.val, ha⟩
  let oldValue := rankMember t (previous input).val (previous input).property
  let newValue := rankMember (rankPointwiseImage j t) (values input).val (values input).property
  have imageValue : j oldValue = newValue := Subtype.ext (previousSpec input)
  have oldEdge : rankGraphApplies old a oldValue :=
    (rankGraphApplies_iff hl _ _ _).mpr ((mem_zfFunctionGraph previous _ _).mpr ⟨ha, rfl⟩)
  have imageEdge : rankGraphApplies (j old) a newValue := by
    rw [← imageValue, ← fixedMembers a ha, rankGraphApplies_iff hl]
    exact (rankElementary_graph_membership_iff hl j a oldValue old).mpr
      ((rankGraphApplies_iff hl _ _ _).mp oldEdge)
  have newEdge : rankGraphApplies s a newValue :=
    (rankGraphApplies_iff hl _ _ _).mpr (zfGraphFunction_edge ((rankIsFunction_iff hl _ _ _).mp function) input)
  obtain ⟨imageOutput, _, _, imageUnique⟩ := imageFunction.2 a ha
  obtain ⟨newOutput, _, _, newUnique⟩ := function.2 a ha
  constructor
  · intro edge
    have same : b = newValue := (imageUnique b edge).trans (imageUnique newValue imageEdge).symm
    exact same ▸ newEdge
  · intro edge
    have same : b = newValue := (newUnique b edge).trans (newUnique newValue newEdge).symm
    exact same ▸ imageEdge

end FullMarkedBLP
