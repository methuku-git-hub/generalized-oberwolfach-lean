module

public import Oberwolfach.FreshNeighbourPairPhysicalEvent

@[expose] public section
/-! The simultaneous endpoint event on one ambient physical sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U K:Type} [Fintype V] [Fintype U] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq K]

def OrdinaryFreshPhysicalEndpointEvent (P B:SimpleGraph (V⊕U))
    (S R:K→Finset (V⊕U)) (g:K→(V⊕U)↪Sym2 (V⊕U)) (p ζ:ℝ)
    (σ:Sym2 (V⊕U)→Bool):Prop:=
  ∀k (S' R':Finset (V⊕U)) (D:SimpleGraph (V⊕U)),S'⊆S k→R'⊆R k→
    ((changed S' ((S k).filter (fun v=>σ (g k v)=true))).card:ℝ)≤ζ*(p*Fintype.card (V⊕U))→
    ((changed R' ((R k).filter (fun v=>σ (g k v)=true))).card:ℝ)≤ζ*(p*Fintype.card (V⊕U))→
    (∀v,(D.degree v:ℝ)≤ζ*(p*Fintype.card (V⊕U)))→S'.card=2*R'.card→
    ∃E:EndpointPairing P B S' R',Disjoint E.graph D
end Oberwolfach
