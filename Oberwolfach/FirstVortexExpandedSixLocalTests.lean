module

public import Oberwolfach.FirstVortexExpandedSixTestsProbability
public import Oberwolfach.MarkedExpandedActualSample

@[expose] public section
/-! Name the six local tests and retain the existing probability estimate
on the original expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]

def FirstVortexExpandedSixLocalTests (G:SimpleGraph V) (π:Equiv.Perm V) (d D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (q s:U→Bool→ℝ) (u ζ:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d):Prop:=
    (∀v,|(((G.neighborFinset v∩Q.extendedVertices 1).filter (fun x=>(z.1 (Sum.inl s(v,x))).1=4)).card:ℝ)-
        u*(G.neighborFinset v∩Q.extendedVertices 1).card|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
      (∀w,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w (Q.extendedVertices 1)-
        ((Q.extendedVertices 1).card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
      (∀v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v (Q.extendedIndices 1)-
        ∑w∈Q.extendedIndices 1,(1-(∑g,q w g)-(∑j,s w j))|<((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
      (∀v∈Q.extendedVertices 1,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) (Q.extendedIndices 1) v).card:ℝ)≤
        4*((Q.extendedIndices 1).card:ℝ)/d+4*((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
      RetainedRestrictionLocalGood π d (fun e=>z.1 (Sum.inr e)) false
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false))
        (Q.extendedVertices 1) (Q.extendedIndices 1) ζ z.2 ∧
      (∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(Fintype.card V:ℝ)^(3/4:ℝ)≤
        (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d (fun e=>z.1 (Sum.inr e)) (x,w)=some (Sum.inr false) ∧
          rawIntervalFamilyState π d (fun e=>z.1 (Sum.inr e)) (y,w)=some (Sum.inr false))).card:ℝ))
end Oberwolfach
