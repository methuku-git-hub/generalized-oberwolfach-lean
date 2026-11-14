module

public import Oberwolfach.OrdinaryNamedDeepCoverSeparateLoadProbability

@[expose] public section
/-! The deterministic local inputs of the deep-cover theorem, named so they
can be verified separately for each fixed vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryDeepCoverLevelInputs
    (m Dmax d:ℕ) (α p ω a ε₀:ℝ) (P F:SimpleGraph V)
    (π:Equiv.Perm V) (J:Finset U) (pR pH D ε:ℝ):Prop where
  J_small:(J.card:ℝ)≤a*Fintype.card V
  hub_lower:ω*Fintype.card V≤((Finset.univ\J).card:ℝ)
  hub_upper:Fintype.card U≤Fintype.card V
  min_degree:∀v,(cycleThreshold (m+1)+α)*Fintype.card V≤(P.degree v:ℝ)
  conflict_degree:∀v,F.degree v≤Dmax
  conflict_contains:permutationConflictGraph π (3*d)≤F
  no_short:∀z l,0<l→l<2*d+1→(π^l) z≠z
  pR_lower:p≤pR
  pR_upper:pR≤1
  pH_lower:p≤pH
  pH_upper:pH≤1
  density_lower:(Fintype.card V:ℝ)/2≤D
  error_nonneg:0≤ε
  error_upper:ε≤ε₀
  approximate_regular:∀v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V
  balance_mean:pR*D=2*Fintype.card U*pH
end Oberwolfach
