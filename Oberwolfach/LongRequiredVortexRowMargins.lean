module

public import Oberwolfach.LongRequiredBoundsFromRows
public import Oberwolfach.MarkedInitialInnerVertexBound
public import Oberwolfach.PartitionMargins

@[expose] public section
/-! The first vortex set and the original n^(3/4) unassigned-row error
supply the required graph bounds after the order is chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_required_vortex_row_margins
    (α lam:ℝ) (hα:0<α) (hlam:0<lam) (d:ℕ) (hd:1≤d):
    ∃ N:ℕ,∀ (V U Γ Color:Type) [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
      [Fintype Γ] [Fintype Color] (P P₀ Sel Used:SimpleGraph V) (Dv m:ℕ) (β ε:ℝ)
      (Q:Vortex U P Dv β ε m),N≤Fintype.card V→
    ∀ (π:Equiv.Perm V) (D M:V→V→Prop)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),
    let I:=Q.extendedVertices 1;
    P₀≤longPhysicalStateGraph P σ {0,1,2,3,4}\Used→
    (∀x∈I,∀y∈I,(longSelectedPhysicalGraph P π d σ).Adj x y→Sel.Adj x y)→
    ∀ (θ C₀ u:ℝ),0≤θ→θ≤1/100→0≤ε→1≤C₀→ε≤α/(1000*C₀)→
    lam≤α/128→0≤u→u≤2*θ→
    (∀v∈I,|(((P.neighborFinset v∩I).filter (fun w=>(σ (Sum.inl s(v,w))).1=4)).card:ℝ)-
      u*(P.neighborFinset v∩I).card|<(Fintype.card V:ℝ)^(3/4:ℝ))→
    (∀v∈I,((longPhysicalStateGraph P σ {2,3}\Used).degree v:ℝ)≤lam*Fintype.card V)→
    (∀v,((longRequiredPhysicalGraph P P₀ Sel π d I D M).degree v:ℝ)≤(α/16)*Fintype.card V) ∧
    ((longRequiredPhysicalGraph P P₀ Sel π d I D M).edgeFinset.card:ℝ)≤
      (θ*ε^2+lam*ε)*(Fintype.card V:ℝ)^2+24*d*Fintype.card V:=by
  obtain ⟨N₁,hN₁⟩:=eventually_sublinear_le_linear (p:=3/4) (ε:=lam) (by norm_num) hlam
  obtain ⟨N₂,hN₂⟩:=exists_nat_gt (1536*(d:ℝ)/α)
  refine ⟨max (max N₁ N₂) 1,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P P₀ Sel Used Dv m β ε Q hn π D M σ I hP₀ hSelected θ C₀ u hθ hθhi he hC hehi hlamhi hu huhi hrow hB
  have hn1:1≤Fintype.card V:=le_trans (le_max_right _ _) hn
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast (show 0<Fintype.card V by omega)
  have hN1:N₁≤Fintype.card V:=le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hN2:N₂≤Fintype.card V:=le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have ht:0≤(Fintype.card V:ℝ)^(3/4:ℝ):=by positivity
  have htbound:=hN₁ (Fintype.card V) hN1
  have hnbound:(1536*(d:ℝ))/α≤Fintype.card V:=by
    have hh:(N₂:ℝ)≤Fintype.card V:=by exact_mod_cast hN2
    linarith
  have hI:((Q.extendedVertices 1).card:ℝ)≤ε*Fintype.card V:=marked_initial_inner_vertex_bound Q he
  have hrow':∀v∈I,|(((P.neighborFinset v∩I).filter (fun w=>(σ (Sum.inl s(v,w))).1=4)).card:ℝ)-
      u*(P.neighborFinset v∩I).card|≤(Fintype.card V:ℝ)^(3/4:ℝ):=by
    intro v hv
    exact (hrow v hv).le
  apply long_required_bounds_from_fixed_inner_rows P P₀ Sel Used π d hd I D M σ hP₀ hSelected
    α θ ε lam ((Fintype.card V:ℝ)^(3/4:ℝ)) C₀ u hα hθ hθhi he hC hehi hlam.le hlamhi ht htbound hnbound hI hu huhi hrow'
  intro v hv
  convert hB v hv using 1 <;> congr!
end Oberwolfach
