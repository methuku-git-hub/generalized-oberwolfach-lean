module

public import Oberwolfach.OrdinaryWheelLikelySeparateCostsCertificate
public import Oberwolfach.OrdinaryTriangleLikelyCoverCertificate

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_triangle_likely_certificate_separate_costs
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (cost deepCost:ℝ)
    (h:OrdinaryTriangleLikelyCoverCertificate Q F H X T Z W cost deepCost):
    OrdinaryWheelLikelySeparateCostsCertificate Q F H X T Z W 3 cost deepCost :=by
  obtain ⟨μ,E,loss,localCost,rate,hn,hloss,hprob,hevent,hlocal,hcost,hdeep⟩:=h
  exact ⟨μ,E,loss,localCost,localCost,hn,hloss,hprob,hevent,hlocal.trans hcost,hlocal.trans hdeep⟩

end Oberwolfach
