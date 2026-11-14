module

public import Oberwolfach.OrdinaryRootCoverSharpReferenceData

@[expose] public section
/-! Package the dependent root-cover witness using one fixed pair of local
vertex and hub types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryRootCoverSharpReferenceExists
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]
    (P Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (r k:ℕ) (hr:3≤r) (cover ell bin cin deep loss α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c:ℝ):Prop :=
  ∃D:OrdinaryRootCoverNonrootData Q F H X T Z W r cover ell,
    Nonempty (OrdinaryRootCoverSharpReferenceData P Q F H X T Z W r k hr cover ell bin cin deep loss D
      α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c)
end Oberwolfach
