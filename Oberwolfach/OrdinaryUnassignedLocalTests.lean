module

public import Oberwolfach.RawUnassignedFixedDomainsAnyError
public import Oberwolfach.ExpandedUnassignedRimAnyError
public import Oberwolfach.FiniteSigmaFirstMap
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! Unassigned physical edges and interval pairs on the protected and full
domains, all read from the same expanded first sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryUnassignedLocalTests
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (q:U→Γ→ℝ) (s:U→Color→ℝ)
    (udens:ℝ) (A:Finset V) (J:Finset U)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):Prop :=
  (∀v,|(((P.neighborFinset v∩A).filter (fun x=>(σ (Sum.inl s(v,x))).1=4)).card:ℝ)-
    udens*(P.neighborFinset v∩A).card|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
  (∀v,|(((P.neighborFinset v).filter (fun x=>(σ (Sum.inl s(v,x))).1=4)).card:ℝ)-
    udens*(P.neighborFinset v).card|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
  (∀w,|rawIntervalUnassignedHubCountOn π d (fun e=>σ (Sum.inr e)) w A-
    (A.card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
  (∀w,|rawIntervalUnassignedHubCountOn π d (fun e=>σ (Sum.inr e)) w Finset.univ-
    (Fintype.card V:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
  (∀v,|rawIntervalUnassignedColumnCount π d (fun e=>σ (Sum.inr e)) v J-
    ∑w∈J,(1-(∑g,q w g)-(∑j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
  (∀v,|rawIntervalUnassignedColumnCount π d (fun e=>σ (Sum.inr e)) v Finset.univ-
    ∑w:U,(1-(∑g,q w g)-(∑j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ))

end Oberwolfach
