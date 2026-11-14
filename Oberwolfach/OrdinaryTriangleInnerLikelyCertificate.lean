module

public import Oberwolfach.OrdinaryTriangleLikelyCoverCertificate
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! Convert an inner-scale cover-down probability into the existing likely
certificate, retaining the actual probability loss and cost bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_inner_likely_certificate
    (Q F:SimpleGraph V) (H:V→U→Prop) (A T:Finset V) (B W:Finset U)
    (μ:FiniteLaw (Sym2 (V⊕U)→Bool)) (E:(Sym2 (V⊕U)→Bool)→Prop)
    (a localCost rate cost deepCost:ℝ)
    (hn:16≤Fintype.card V) (hA:0<A.card) (hloss:a+1/(A.card:ℝ)≤1/4)
    (hprob:1-a-(1/(A.card:ℝ)+1/(Fintype.card (V⊕U):ℝ))-
      1/(Fintype.card (V⊕U):ℝ)≤μ.probability E)
    (hcover:∀σ,E σ→OrdinaryProtectedHostCoverDownResult Q F H A T B W 3 localCost localCost)
    (hlocal:localCost≤rate*Fintype.card (V⊕U))
    (hcost:rate*Fintype.card (V⊕U)≤cost) (hdeep:rate*Fintype.card (V⊕U)≤deepCost):
    OrdinaryTriangleLikelyCoverCertificate Q F H A T B W cost deepCost:=by
  refine ⟨μ,E,a+1/(A.card:ℝ),localCost,rate,hn,hloss,?_,hcover,hlocal,hcost,hdeep⟩
  have hnV:(0:ℝ)≤1/(Fintype.card V:ℝ):=by positivity
  have hnW:(0:ℝ)≤1/(Fintype.card (V⊕U):ℝ):=by positivity
  have heq:2/(Fintype.card (V⊕U):ℝ)=2*(1/(Fintype.card (V⊕U):ℝ)):=by ring
  linarith only [hprob,hnV,hnW,heq]
end Oberwolfach
