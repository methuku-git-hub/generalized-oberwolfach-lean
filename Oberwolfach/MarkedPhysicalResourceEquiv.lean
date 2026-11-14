module

public import Oberwolfach.MarkedWheelVertexEmbedding

@[expose] public section
/-! A bijection of rows and hubs induces a bijection of physical resources. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U':Type} [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']

def markedPhysicalResourceEquiv (f:V≃V') (g:U≃U') :
    (Finset V ⊕ (V×U)) ≃ (Finset V' ⊕ (V'×U')) :=
  (Equiv.finsetCongr f).sumCongr (Equiv.prodCongr f g)

theorem marked_physical_resource_equiv_apply (f:V≃V') (g:U≃U')
    (a:Finset V⊕(V×U)) :
    markedPhysicalResourceEquiv f g a = markedResourceEmbedding f.toEmbedding g.toEmbedding a := by
  cases a with
  | inl s =>
    change Sum.inl (Finset.map f.toEmbedding s) = Sum.inl (Finset.image f s)
    exact congrArg Sum.inl (Finset.map_eq_image _ _)
  | inr vu =>
    cases vu
    rfl
end Oberwolfach
