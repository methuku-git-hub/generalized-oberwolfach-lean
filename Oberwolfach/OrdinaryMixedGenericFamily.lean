module

public import Oberwolfach.MarkedOrdinaryResourceLoads

@[expose] public section
/-! Generic marked and unmarked candidate families in one typed resource
universe; the option index records which family supplied a candidate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V U CM:Type} {CO:I→Type} [Fintype I] [Fintype V] [Fintype U]
  [LinearOrder V] [DecidableEq U] [Fintype CM] [∀i,Fintype (CO i)]

abbrev OrdinaryMixedGenericFamily (CM:Type) (CO:I→Type):Option I→Type
  | none=>CM
  | some i=>CO i

instance ordinaryMixedGenericFamilyFintype : ∀i,Fintype (OrdinaryMixedGenericFamily CM CO i)
  | none=>inferInstance
  | some _=>inferInstance

def ordinaryMixedGenericResources
    (RM:CM→Finset (((V×V)⊕(V×V))⊕(Bool×V×U)))
    (RO:∀i,CO i→Finset ((V×V)⊕(V×U))):
    ∀i,OrdinaryMixedGenericFamily CM CO i→Finset (((V×V)⊕(V×V))⊕(Bool×V×U))
  | none,c=>RM c
  | some i,c=>(RO i c).map ordinaryMarkedResourceEmbedding

def ordinaryMixedGenericWeight (wM:CM→ℝ) (wO:∀i,CO i→ℝ):
    ∀i,OrdinaryMixedGenericFamily CM CO i→ℝ
  | none,c=>wM c
  | some i,c=>wO i c
end Oberwolfach
