module

public import Oberwolfach.LongApproximateResidualFromResources
public import Oberwolfach.LongRequiredVortexRowMargins

@[expose] public section
/-! The first-vortex required graph bounds from the original approximate
matching coverage, with no separately supplied unused-edge degree bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_required_vortex_rows_from_matching
    (α lam:ℝ) (hα:0<α) (hlam:0<lam) (d:ℕ) (hd:1≤d):
    ∃ N:ℕ,∀ (V U Γ Color:Type) [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
      [Fintype Γ] [Fintype Color] (P P₀ Sel:SimpleGraph V) (Dv m:ℕ) (β ε:ℝ)
      (Q:Vortex U P Dv β ε m),N≤Fintype.card V→
    ∀ (π:Equiv.Perm V) (D M:V→V→Prop)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) (g:Γ) (j:Color),
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀ (C:Type) [Fintype C] [DecidableEq C]
      (R:C→Finset {z // z∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d raw)
        (rawMarkedPairSpokes π d raw g j))}) (matchSet:Finset C),
    let Used:=physicalRimCandidateUnion φ R matchSet
    let I:=Q.extendedVertices 1
    P₀≤longPhysicalStateGraph P σ {0,1,2,3,4}\Used→
    (∀x∈I,∀y∈I,(longSelectedPhysicalGraph P π d σ).Adj x y→Sel.Adj x y)→
    ∀ (θ C₀ u a γ:ℝ),0≤θ→θ≤1/100→0≤ε→1≤C₀→ε≤α/(1000*C₀)→
    lam≤α/128→0≤u→u≤2*θ→0≤γ→a≤lam/2→γ≤lam/2→
    (∀v∈I,|(((P.neighborFinset v∩I).filter (fun w=>(σ (Sum.inl s(v,w))).1=4)).card:ℝ)-
      u*(P.neighborFinset v∩I).card|<(Fintype.card V:ℝ)^(3/4:ℝ))→
    (∀x,a*(Fintype.card V:ℝ)≤(rimIncidentResources φ x).card →
      (((rimIncidentResources φ x\matchSet.biUnion R).card:ℕ):ℝ)≤γ*(rimIncidentResources φ x).card) →
    (∀v,((longRequiredPhysicalGraph P P₀ Sel π d I D M).degree v:ℝ)≤(α/16)*Fintype.card V) ∧
    ((longRequiredPhysicalGraph P P₀ Sel π d I D M).edgeFinset.card:ℝ)≤
      (θ*ε^2+lam*ε)*(Fintype.card V:ℝ)^2+24*d*Fintype.card V:=by
  obtain ⟨N₁,hN₁⟩:=long_required_vortex_row_margins α lam hα hlam d hd
  obtain ⟨N₂,hN₂⟩:=exists_nat_gt (2*((6*d+2:ℕ):ℝ)/lam)
  refine ⟨max N₁ N₂,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P P₀ Sel Dv m β ε Q hn π D M σ g j raw φ C _ _ R matchSet Used I hP₀ hSel θ C₀ u a γ hθ hθhi he hC hehi hlamhi hu huhi hγ ha hγhi hrow hlarge
  have hN1:N₁≤Fintype.card V:=le_trans (le_max_left _ _) hn
  have hN2:N₂≤Fintype.card V:=le_trans (le_max_right _ _) hn
  have hN2r:(N₂:ℝ)≤Fintype.card V:=by exact_mod_cast hN2
  have hlin:((6*d+2:ℕ):ℝ)≤(lam/2)*(Fintype.card V:ℝ):=by
    have hcalc:2*((6*d+2:ℕ):ℝ)/lam≤Fintype.card V:=le_trans (le_of_lt hN₂) hN2r
    have hh:2*((6*d+2:ℕ):ℝ)≤(Fintype.card V:ℝ)*lam:=(div_le_iff₀ hlam).mp hcalc
    linarith
  have hmax:max a γ≤lam/2:=max_le ha hγhi
  have hnnonneg:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
  have hsmall:max a γ*(Fintype.card V:ℝ)≤(lam/2)*(Fintype.card V:ℝ):=mul_le_mul_of_nonneg_right hmax hnnonneg
  have hB:∀v∈I,((longPhysicalStateGraph P σ {2,3}\Used).degree v:ℝ)≤lam*Fintype.card V:=by
    intro v hv
    have hh:=long_approximate_unused_degree_from_matching P π d σ g j a γ hγ C R matchSet hlarge v
    dsimp only [raw,φ,Used] at *
    linarith
  exact hN₁ V U Γ Color P P₀ Sel Used Dv m β ε Q hN1 π D M σ hP₀ hSel θ C₀ u hθ hθhi he hC hehi hlamhi hu huhi hrow hB
end Oberwolfach
