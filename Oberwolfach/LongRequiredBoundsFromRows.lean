module

public import Oberwolfach.LongPreparationPhysicalContainment
public import Oberwolfach.LongUnassignedInnerDegree

@[expose] public section
/-! Use the sampled fixed-inner-domain unassigned row estimate at its
original scale, rather than requiring a global unassigned degree bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem long_required_bounds_from_fixed_inner_rows
    (P P₀ Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (hd:1≤d) (I:Finset V) (D M:V→V→Prop)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (hP₀:P₀≤longPhysicalStateGraph P σ {0,1,2,3,4}\Used)
    (hSelected:∀x∈I,∀y∈I,(longSelectedPhysicalGraph P π d σ).Adj x y→Sel.Adj x y)
    (α θ ε lam t C₀ u:ℝ) (hα:0<α) (hθ:0≤θ) (hθhi:θ≤1/100)
    (he:0≤ε) (hC:1≤C₀) (hehi:ε≤α/(1000*C₀))
    (hlam:0≤lam) (hlamhi:lam≤α/128) (ht:0≤t) (htbound:t≤lam*Fintype.card V)
    (hn:(1536*(d:ℝ))/α≤Fintype.card V)
    (hI:(I.card:ℝ)≤ε*Fintype.card V) (hu:0≤u) (huhi:u≤2*θ)
    (hrow:∀v∈I,|(((P.neighborFinset v∩I).filter (fun w=>(σ (Sum.inl s(v,w))).1=4)).card:ℝ)-
      u*(P.neighborFinset v∩I).card|≤t)
    (hB:∀v∈I,((longPhysicalStateGraph P σ {2,3}\Used).degree v:ℝ)≤lam*Fintype.card V):
    (∀v,((longRequiredPhysicalGraph P P₀ Sel π d I D M).degree v:ℝ)≤(α/16)*Fintype.card V) ∧
    ((longRequiredPhysicalGraph P P₀ Sel π d I D M).edgeFinset.card:ℝ)≤
      (θ*ε^2+lam*ε)*(Fintype.card V:ℝ)^2+24*d*Fintype.card V:=by
  let U₀:=longPhysicalStateGraph P σ {4}
  let UI:=spanningRestriction U₀ I
  have hA:∀v∈I,(UI.degree v:ℝ)≤2*θ*I.card+t:=
    long_unassigned_restricted_degree_from_row P I σ u θ t hu hθ huhi hrow
  have hidem:spanningRestriction UI I=spanningRestriction U₀ I:=by
    ext x y
    simp only [spanningRestriction_adj,UI,and_assoc,and_self]
  have hSub:=long_required_physical_containment P P₀ Sel Used π d I D M σ hP₀ hSelected
  rw [←hidem] at hSub
  apply long_preparation_bad_graph_margins P (longRequiredPhysicalGraph P P₀ Sel π d I D M)
    (longPhysicalStateGraph P σ {2,3}\Used) UI π d hd I
    α θ ε lam t C₀ hα hθ hθhi he hC hehi hlam hlamhi ht htbound hn hI hA
  · intro v hv
    convert hB v hv using 1 <;> congr!
  · exact hSub
end Oberwolfach
