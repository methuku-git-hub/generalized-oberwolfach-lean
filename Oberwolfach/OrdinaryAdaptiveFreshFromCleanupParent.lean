module

public import Oberwolfach.OrdinaryAdaptiveFreshFromNonemptyParent
public import Oberwolfach.OrdinaryParentExtensionsFromProfile

@[expose] public section
/-! A matched earlier outcome with a cleanup profile and nonempty corrected
parent extends to one fresh reserve/factor/cleanup sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_fresh_from_cleanup_parent_event
    (γ κ b B:ℝ) (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (q:ℕ)
      (εres εsup βe βh:ℝ) (hres:0<εres) (hsup:0<εsup) (hβe:0<βe) (hβh:0<βh),∃N:ℕ,
    ∀(V U Ω Γ Color:Type) [Fintype V] [Fintype U] [Fintype Ω] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e₀:ℝ),1-e₀≤μ.probability E→
    ∀(P Q₀ F:Ω→SimpleGraph V) (H₀:Ω→V→U→Prop) (X:Ω→Finset V) (Z:Ω→Finset U)
      (π:Equiv.Perm V) (d:ℕ) (s:U→Color→ℝ) (j:Color) (raw:Ω→RawWheelOutcome V U Γ Color)
      (pR pH density tR tH Ledit:ℝ),
    let Q:=fun ω=>spanningRestriction (Q₀ ω) (X ω);
    let H:=fun ω v u=>H₀ ω v u ∧ v∈X ω ∧ u∈Z ω;
    (∀ω,E ω→OrdinaryCleanupParentProfiles (P ω) (Q₀ ω) (F ω) (H₀ ω) π d (X ω) (Z ω)
      pR pH density tR tH Ledit βe βh s j (raw ω))→
    ∀(parent:∀ω,E ω→Nonempty (MixedFreshParentDataInsideRoots γ κ b B ε η (Q ω) (F ω)
      (ordinaryPhysicalGraph (Q ω) (H ω)) (ordinaryPhysicalGraph (F ω) (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H₀ ω) (Z ω) (X ω))
      (fun i=>(ordinaryBoundaryRimSet (Q₀ ω) (X ω) i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet (H₀ ω) (X ω) (Z ω) i).image Sum.inr))),
    let data:=fun ω (h:E ω)=>Classical.choice (parent ω h);
    let ν:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-(e₀+4/(Fintype.card (V⊕U):ℝ)^q+1/(Fintype.card V:ℝ)^q)≤
      (μ.sigma (fun _=>ν)).probability (fun z=>E z.1 ∧
        OrdinaryBoundaryReserveGood (Q₀ z.1) (H₀ z.1) (X z.1) (Z z.1) p εres z.2 ∧
        BoundaryReserveSupportGood (ordinaryBoundaryGraph (Q₀ z.1) (H₀ z.1) (X z.1) (Z z.1)) p εsup z.2 ∧
        (∃hE:E z.1,MixedFreshBoundaryAvoidingEvent p ρ ζ (Q z.1) (F z.1)
          (ordinaryPhysicalGraph (Q z.1) (H z.1)) (ordinaryPhysicalGraph (F z.1) (fun _ _=>False))
          (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H₀ z.1) (Z z.1) (X z.1))
          (fun i=>(ordinaryBoundaryRimSet (Q₀ z.1) (X z.1) i).image Sum.inl)
          (fun i=>(ordinaryBoundaryRowSet (H₀ z.1) (X z.1) (Z z.1) i).image Sum.inr)
          (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val))
          (data z.1 hE).endpoint_disjoint z.2) ∧
        OrdinaryBoundaryExtensionGood (Q₀ z.1) (H₀ z.1) (X z.1) βe p z.2 ∧
        OrdinaryBoundaryHubPairGood (H₀ z.1) (Z z.1) βh p z.2) := by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hmain⟩:=ordinary_adaptive_fresh_triangle_from_nonempty_parent γ κ b B hγ hκ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 ρ hρ q εres εsup βe βh hres hsup hβe hβh
  obtain ⟨N,hN⟩:=hmain p hp hp1 ρ hρ q εres εsup βe βh hres hsup hβe hβh
  refine ⟨N,?_⟩
  intro V U Ω Γ Color _ _ _ _ _ _ _ hn hu μ E e₀ hE P Q₀ F H₀ X Z π d s j raw
    pR pH density tR tH Ledit Q H hprofiles parent data ν
  have hparent:∀ω,E ω→∀a c u,βe*Fintype.card (V⊕U)≤
      (((X ω).filter (fun v=>(Q₀ ω).Adj a v∧(Q₀ ω).Adj v c∧H₀ ω v u)).card:ℝ):=by
    intro ω hω
    exact ordinary_parent_extensions_from_profile (P ω) (Q₀ ω) (F ω) (H₀ ω) (X ω) (Z ω) π d j s
      pR pH density tR tH Ledit βe βh (raw ω) (hprofiles ω hω)
  exact hN V U Ω hn hu μ E e₀ hE Q₀ Q F H₀ H X Z parent hparent
end Oberwolfach
