module

public import Oberwolfach.OrdinaryMixedHubWeightsFromInducedGeneral

@[expose] public section
/-! Fixed inner-domain data needed to turn local sampled potentials into
mixed hub weights. All fields are explicit and independent of later edits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

structure OrdinaryInnerHubWeightSetupGeneral (m:ℕ)
    (P F : SimpleGraph V) (A : Finset V) (weight : OrdinaryCycle (P.induce (A : Set V)) (m+1) → ℝ)
    (p pR pH D δ ξ L cLo cHi b B η K : ℝ) : Prop where
  Apos : 0<A.card
  ppos : 0<p
  pone : p≤1
  rimlo : p≤pR
  rimhi : pR≤1
  spokelo : p≤pH
  spokehi : pH≤1
  delta_nonneg : 0≤δ
  conflict_nonneg : 0≤L
  lower_pos : 0<cLo
  upper_nonneg : 0≤cHi
  scale_nonneg : 0≤K
  center_lower : (A.card:ℝ)/2≤D
  center_upper : D≤2*A.card
  regular : ∀v:{v:V // v∈(A:Set V)},|((P.induce (A:Set V)).degree v:ℝ)-D|≤δ*A.card
  conflict : ∀v:{v:V // v∈(A:Set V)},((F.induce (A:Set V)).degree v:ℝ)≤L
  coefficients : ∀C,cLo/(A.card:ℝ)^(m-1)≤weight C ∧ weight C≤cHi/(A.card:ℝ)^(m-1)
  edge_loads : ∀x y,(∑C,if C.val.val.Adj x y then weight C else 0)=if (P.induce (A:Set V)).Adj x y then 1 else 0
  domain_scale : (Fintype.card V:ℝ)≤K*A.card
  lower_scale : b≤cLo
  upper_scale : (4*cHi/p^(3*m+1))*K^m≤B
  error_margin : ξ+2*δ+12*((m+1:ℕ):ℝ)^4*cHi*L/A.card≤η
end Oberwolfach
