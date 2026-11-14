module

public import Oberwolfach.OrdinaryNearBalancePacking

@[expose] public section
/-! Explicit structural input to the near-balance ordinary packing theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryNearBalancePackingData (r:ℕ) (hr:3≤r) (k:ℕ) (α ω β bminus bplus h δ εstar η:ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) where
  hub_lower:ω*Fintype.card V≤Fintype.card U
  hub_upper:Fintype.card U≤Fintype.card V
  graph_sub:Q≤P\F
  orientation:V→V→ℕ
  orientation_graph:∀x y,orientation x y+orientation y x=if Q.Adj x y then 1 else 0
  rim_cuts:BipartiteLargeCut orientation δ h
  spoke_cuts:BipartiteLargeCut (fun v u=>if H v u then 1 else 0) δ h
  spoke_degree:∀v,β*Fintype.card V≤((Finset.univ.filter (H v)).card:ℝ)
  balance:∀v,|(Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card|≤η*Fintype.card V
  isolators:∀x y,Q.Adj x y→β*(Fintype.card V:ℝ)^(k-1)≤
    (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k (max (1/2) (cycleThreshold r)) (α/4) x y):ℝ)
  transfers:∀v (i j:{u // H v u}),i.val≠j.val→β*(Fintype.card V:ℝ)^(r^2)≤
    (Fintype.card (OrdinaryTransferConfiguration hr Q F H v i.val j.val):ℝ)
  weight:OrdinaryWheel Q F H r→ℝ
  weight_bounds:∀W,bminus/(Fintype.card V:ℝ)^(r-1)≤weight W ∧ weight W≤bplus/(Fintype.card V:ℝ)^(r-1)
  rim_load:∀x y,Q.Adj x y→|ordinaryRimLoad weight x y-1|≤εstar
  spoke_load:∀v u,H v u→|ordinarySpokeLoad weight v u-1|≤εstar
end Oberwolfach
