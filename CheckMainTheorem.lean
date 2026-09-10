import FullMarkedBLP

open FullMarkedBLP

/-- Check the final theorem against the literal generated domain and the
explicit two-level list key, without an auxiliary acceptance predicate. -/
example (i2 : RankI2.{u}) :
    WellFounded (fun child parent : {a : List Row // Generated a} =>
      Step parent.val child.val) ∧
    IsWellOrder {a : List Row // Generated a}
      (fun a b =>
        a.val.map (fun row => (row.core.drop row.step).reverse ++ row.core.take 1) <
        b.val.map (fun row => (row.core.drop row.step).reverse ++ row.core.take 1)) ∧
    Function.Injective
      (fun a : {a : List Row // Generated a} =>
        a.val.map (fun row => (row.core.drop row.step).reverse ++ row.core.take 1)) ∧
    (∀ a b : {a : List Row // Generated a}, shortKey b.val ≤ shortKey a.val ↔
      Relation.ReflTransGen Step a.val b.val) :=
  rankI2_full_marked_blp_natural_cutoff_wellorder i2

#print axioms FullMarkedBLP.rankI2_full_marked_blp_natural_cutoff_wellorder
#print axioms FullMarkedBLP.exists_full_root_of_rankI2
#print axioms FullMarkedBLP.step_shortKey_lt
