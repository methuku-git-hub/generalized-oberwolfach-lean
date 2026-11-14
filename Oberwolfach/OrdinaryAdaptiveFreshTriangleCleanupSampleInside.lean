module

public import Oberwolfach.OrdinaryAdaptiveFreshTriangleExtraInside
public import Oberwolfach.OrdinaryBoundaryLocalEvents

@[expose] public section
/-! A single adaptive physical sample supplies reserve profiles, support,
fresh triangle factors and the local sparse-cleanup extension events. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_fresh_triangle_cleanup_sample_inside
    (γ κ b B:ℝ) (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (q:ℕ)
      (εres εsup βe βh:ℝ) (hres:0<εres) (hsup:0<εsup) (hβe:0<βe) (hβh:0<βh),∃N:ℕ,
    ∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e₀:ℝ),1-e₀≤μ.probability E→
    ∀(Q₀ Q F:Ω→SimpleGraph V) (H₀ H:Ω→V→U→Prop) (X:Ω→Finset V) (Z:Ω→Finset U),
    ∀(data:∀ω,E ω→MixedFreshParentDataInsideRoots γ κ b B ε η (Q ω) (F ω)
      (ordinaryPhysicalGraph (Q ω) (H ω)) (ordinaryPhysicalGraph (F ω) (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H₀ ω) (Z ω) (X ω))
      (fun i=>(ordinaryBoundaryRimSet (Q₀ ω) (X ω) i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet (H₀ ω) (X ω) (Z ω) i).image Sum.inr)),
    (∀ω,E ω→∀a c u,βe*Fintype.card (V⊕U)≤
      (((X ω).filter (fun v=>(Q₀ ω).Adj a v∧(Q₀ ω).Adj v c∧H₀ ω v u)).card:ℝ))→
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
        OrdinaryBoundaryHubPairGood (H₀ z.1) (Z z.1) βh p z.2):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hmain⟩:=ordinary_adaptive_fresh_triangle_sample_with_extra_inside γ κ b B hγ hκ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 ρ hρ q εres εsup βe βh hres hsup hβe hβh
  obtain ⟨Nm,hNm⟩:=hmain p hp hp1 ρ hρ q εres εsup hres hsup
  obtain ⟨Nl,hNl⟩:=ordinary_boundary_local_events_high_probability βe βh p hβe hβh hp hp1 q
  refine ⟨max Nm Nl,?_⟩
  intro V U Ω _ _ _ _ _ hn hu μ E e₀ hE Q₀ Q F H₀ H X Z data hparent ν
  have hnW:Fintype.card V≤Fintype.card (V⊕U):=Fintype.card_le_of_injective Sum.inl Sum.inl_injective
  let Other:Ω→(Sym2 (V⊕U)→Bool)→Prop:=fun ω σ=>
    OrdinaryBoundaryExtensionGood (Q₀ ω) (H₀ ω) (X ω) βe p σ ∧
      OrdinaryBoundaryHubPairGood (H₀ ω) (Z ω) βh p σ
  have hOther:∀ω,E ω→1-2/(Fintype.card (V⊕U):ℝ)^q≤ν.probability (Other ω):=by
    intro ω hω
    exact hNl V U (by omega) (Q₀ ω) (H₀ ω) (X ω) (Z ω) (hparent ω hω)
  have hh:=hNm V U Ω (by omega) hu μ E e₀ hE Q₀ Q F H₀ H X Z data Other
    (2/(Fintype.card (V⊕U):ℝ)^q) (by positivity) hOther
  convert hh using 1 <;> try ring
end Oberwolfach
