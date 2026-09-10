import Mathlib.Logic.Relation

namespace FullMarkedBLP

/-- In a terminating relation whose immediate branches are nested by
reachability, every pair of descendants is comparable by reachability.
This induction does not presume injectivity of any comparison key. -/
theorem accessible_descendants_comparable {alpha : Sort u} {r : alpha → alpha → Prop}
    (branches : ∀ a x y, r a x → r a y →
      Relation.ReflTransGen r x y ∨ Relation.ReflTransGen r y x)
    {root : alpha} (accessible : Acc (fun child parent => r parent child) root) :
    ∀ a b, Relation.ReflTransGen r root a → Relation.ReflTransGen r root b →
      Relation.ReflTransGen r a b ∨ Relation.ReflTransGen r b a := by
  induction accessible with
  | intro root previous ih =>
    intro a b toA toB
    rcases toA.cases_head with rfl | ⟨x, firstA, restA⟩
    · exact Or.inl toB
    rcases toB.cases_head with rfl | ⟨y, firstB, restB⟩
    · exact Or.inr toA
    rcases branches root x y firstA firstB with xy | yx
    · exact ih x firstA a b restA (xy.trans restB)
    · exact ih y firstB a b (yx.trans restA) restB

end FullMarkedBLP
