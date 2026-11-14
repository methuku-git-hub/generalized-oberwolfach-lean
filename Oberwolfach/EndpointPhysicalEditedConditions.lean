module

public import Oberwolfach.EndpointPhysicalPotentialEvent

@[expose] public section
/-! Explicit geometric, degree, balance and edit inputs for the physical
endpoint factor after the common raw sample has been edited. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

structure EndpointPhysicalEditedConditions (P Q F:SimpleGraph V) (H:V→U→Prop)
    (A:Finset V) (B:Finset U) (X:Finset V) (π:Equiv.Perm V) (d:ℕ) (j:Color)
    (κ p pR pH L Ledit δ:ℝ) (σ:RawWheelOutcome V U Γ Color):Prop where
  row_pos:0<A.card
  rim_sub:(ordinaryPhysicalGraph (U:=U) Q (fun _ _=>False))≤
    (ordinaryPhysicalGraph P (fun _ _=>False))\(ordinaryPhysicalGraph F (fun _ _=>False))
  kappa_pos:0<κ
  p_pos:0<p
  conflict_nonneg:0≤L
  edit_nonneg:0≤Ledit
  balance_nonneg:0≤δ
  index_lower:κ*A.card≤(B.card:ℝ)
  index_upper:B.card≤A.card
  rim_lower:p≤pR
  rim_upper:pR≤1
  spoke_lower:p≤pH
  spoke_upper:pH≤1
  conflict_degree:∀v:V⊕U,((ordinaryPhysicalGraph F (fun _ _=>False)).degree v:ℝ)≤L
  parent_balance:∀x∈X,|pR*(A∩P.neighborFinset x).card/(2*B.card*pH)-1|≤δ
  rim_edit:∀v:V⊕U,((changed
    ((ordinaryPhysicalGraph (rawWheelGraph P σ) (fun _ _=>False)).neighborFinset v)
    ((ordinaryPhysicalGraph Q (fun _ _=>False)).neighborFinset v)).card:ℝ)≤Ledit
  spoke_edit:∀v:V⊕U,((changed
    ((ordinaryPhysicalGraph ⊥ (rawWheelSpokes π d σ j)).neighborFinset v)
    ((ordinaryPhysicalGraph ⊥ H).neighborFinset v)).card:ℝ)≤Ledit
end Oberwolfach
