module

public import Oberwolfach.LongRequiredBoundsFromRows
public import Oberwolfach.LongPreparationBadGraphBounds

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_required_degree_precise_from_fixed_inner_rows
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P P₀ Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (D M:V→V→Prop)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (hP₀:P₀≤longPhysicalStateGraph P σ {0,1,2,3,4}\Used)
    (hSelected:∀x∈I,∀y∈I,(longSelectedPhysicalGraph P π d σ).Adj x y→Sel.Adj x y)
    (θ lam t u:ℝ) (hθ:0≤θ) (hlam:0≤lam) (ht:0≤t) (hu:0≤u) (huhi:u≤2*θ)
    (hrow:∀v∈I,|(((P.neighborFinset v∩I).filter (fun w=>(σ (Sum.inl s(v,w))).1=4)).card:ℝ)-
      u*(P.neighborFinset v∩I).card|≤t)
    (hB:∀v∈I,((longPhysicalStateGraph P σ {2,3}\Used).degree v:ℝ)≤lam*Fintype.card V):
    ∀v,((longRequiredPhysicalGraph P P₀ Sel π d I D M).degree v:ℝ)≤
      2*θ*I.card+t+lam*Fintype.card V+(6*d+2:ℕ):=by
  let U₀:=longPhysicalStateGraph P σ {4}
  let UI:=spanningRestriction U₀ I
  have hA:∀v∈I,(UI.degree v:ℝ)≤2*θ*I.card+t:=
    long_unassigned_restricted_degree_from_row P I σ u θ t hu hθ huhi hrow
  have hidem:spanningRestriction UI I=spanningRestriction U₀ I:=by
    ext x y
    simp only [spanningRestriction_adj,UI,and_assoc,and_self]
  have hSub:=long_required_physical_containment P P₀ Sel Used π d I D M σ hP₀ hSelected
  rw [←hidem] at hSub
  have ha:0≤2*θ*(I.card:ℝ)+t:=by positivity
  have hb:0≤lam*(Fintype.card V:ℝ):=by positivity
  exact (long_preparation_bad_graph_bounds P (longRequiredPhysicalGraph P P₀ Sel π d I D M)
    (longPhysicalStateGraph P σ {2,3}\Used) UI π d I (2*θ*I.card+t) (lam*Fintype.card V)
    ha hb hA (by intro v hv; convert hB v hv using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _) hSub).1
end Oberwolfach
