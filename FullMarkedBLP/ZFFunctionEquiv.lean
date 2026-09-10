import FullMarkedBLP.FunctionGraphConstruction

namespace FullMarkedBLP

theorem zfGraphFunction_value_exists {x y f : ZFSet.{u}} (hf : ZFSet.IsFunc x y f) (a : x) :
    ∃ b : y, ZFSet.pair a.val b.val ∈ f := by
  obtain ⟨b, edge, _⟩ := hf.2 a.val a.property
  exact ⟨⟨b, (ZFSet.pair_mem_prod.mp (hf.1 edge)).2⟩, edge⟩

/-- Recover the ordinary function represented by a genuine ZF function graph. -/
noncomputable def zfGraphFunction {x y f : ZFSet.{u}} (hf : ZFSet.IsFunc x y f) : x → y :=
  fun a => Classical.choose (zfGraphFunction_value_exists hf a)

theorem zfGraphFunction_edge {x y f : ZFSet.{u}} (hf : ZFSet.IsFunc x y f) (a : x) :
    ZFSet.pair a.val (zfGraphFunction hf a).val ∈ f :=
  Classical.choose_spec (zfGraphFunction_value_exists hf a)

theorem zfGraphFunction_unique {x y f : ZFSet.{u}} (hf : ZFSet.IsFunc x y f)
    (a : x) (b : y) (edge : ZFSet.pair a.val b.val ∈ f) : zfGraphFunction hf a = b := by
  apply Subtype.ext
  obtain ⟨v, _, unique⟩ := hf.2 a.val a.property
  exact (unique _ (zfGraphFunction_edge hf a)).trans (unique _ edge).symm

theorem zfGraphFunction_graph {x y : ZFSet.{u}} (g : x → y) :
    zfGraphFunction (zfFunctionGraph_isFunc g) = g := by
  funext a
  exact zfGraphFunction_unique (zfFunctionGraph_isFunc g) a (g a)
    ((mem_zfFunctionGraph g _ _).mpr ⟨a.property, rfl⟩)

theorem zfFunctionGraph_recovered {x y f : ZFSet.{u}} (hf : ZFSet.IsFunc x y f) :
    zfFunctionGraph (zfGraphFunction hf) = f := by
  apply ZFSet.ext
  intro p
  constructor
  · intro member
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp member
    exact zfGraphFunction_edge hf a
  · intro member
    obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp (hf.1 member)
    apply (mem_zfFunctionGraph (zfGraphFunction hf) _ _).mpr
    exact ⟨ha, congrArg Subtype.val (zfGraphFunction_unique hf ⟨a, ha⟩ ⟨b, hb⟩ member)⟩

/-- An equivalence between ordinary functions and members of the actual
ZF function-space set. This also certifies that all function graphs occur. -/
noncomputable def zfFunctionEquiv (x y : ZFSet.{u}) : (x → y) ≃ ZFSet.funs x y where
  toFun g := ⟨zfFunctionGraph g, ZFSet.mem_funs.mpr (zfFunctionGraph_isFunc g)⟩
  invFun f := zfGraphFunction (ZFSet.mem_funs.mp f.property)
  left_inv g := zfGraphFunction_graph g
  right_inv f := Subtype.ext (zfFunctionGraph_recovered (ZFSet.mem_funs.mp f.property))

end FullMarkedBLP
