module

public import Oberwolfach.MixedFreshParentDataInsideRoots
public import Oberwolfach.OrdinaryAdaptiveReserveSupportExtra
public import Oberwolfach.OrdinaryBoundaryFactorClassesAfterPacking

@[expose] public section
/-! A prior outcome, its adaptive reserve and support estimates, and the
mixed triangle factor event all occur on one physical-edge sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_fresh_triangle_sample_with_extra_inside
    (γ κ b B:ℝ) (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (q:ℕ)
      (εres εsup:ℝ) (hres:0<εres) (hsup:0<εsup),∃N:ℕ,
    ∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e₀:ℝ),1-e₀≤μ.probability E→
    ∀(Q₀ Q F:Ω→SimpleGraph V) (H₀ H:Ω→V→U→Prop) (X:Ω→Finset V) (Z:Ω→Finset U),
    ∀(data:∀ω,E ω→MixedFreshParentDataInsideRoots γ κ b B ε η (Q ω) (F ω)
      (ordinaryPhysicalGraph (Q ω) (H ω)) (ordinaryPhysicalGraph (F ω) (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H₀ ω) (Z ω) (X ω))
      (fun i=>(ordinaryBoundaryRimSet (Q₀ ω) (X ω) i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet (H₀ ω) (X ω) (Z ω) i).image Sum.inr)),
    let ν:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    ∀(Other:Ω→(Sym2 (V⊕U)→Bool)→Prop) (δ:ℝ),0≤δ→
    (∀ω,E ω→1-δ≤ν.probability (Other ω))→
    1-(e₀+2/(Fintype.card (V⊕U):ℝ)^q+1/(Fintype.card V:ℝ)^q+δ)≤
      (μ.sigma (fun _=>ν)).probability (fun z=>E z.1 ∧
        OrdinaryBoundaryReserveGood (Q₀ z.1) (H₀ z.1) (X z.1) (Z z.1) p εres z.2 ∧
        BoundaryReserveSupportGood (ordinaryBoundaryGraph (Q₀ z.1) (H₀ z.1) (X z.1) (Z z.1)) p εsup z.2 ∧
        (∃hE:E z.1,MixedFreshBoundaryAvoidingEvent p ρ ζ (Q z.1) (F z.1)
          (ordinaryPhysicalGraph (Q z.1) (H z.1)) (ordinaryPhysicalGraph (F z.1) (fun _ _=>False))
          (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H₀ z.1) (Z z.1) (X z.1))
          (fun i=>(ordinaryBoundaryRimSet (Q₀ z.1) (X z.1) i).image Sum.inl)
          (fun i=>(ordinaryBoundaryRowSet (H₀ z.1) (X z.1) (Z z.1) i).image Sum.inr)
          (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val))
          (data z.1 hE).endpoint_disjoint z.2) ∧ Other z.1 z.2):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hfactor⟩:=mixed_fresh_boundary_probability_from_inside_parent γ κ b B hγ hκ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 ρ hρ q εres εsup hres hsup
  obtain ⟨Nf,hNf⟩:=hfactor p hp hp1 ρ hρ q
  obtain ⟨Nr,hNr⟩:=ordinary_adaptive_reserve_support_and_extra q εres εsup hres hsup
  refine ⟨max 2 (max Nf Nr),?_⟩
  intro V U Ω _ _ _ _ _ hn hu μ E e₀ hE Q₀ Q F H₀ H X Z data ν Other δ hδ hOther
  have hnW:Fintype.card V≤Fintype.card (V⊕U):=Fintype.card_le_of_injective Sum.inl Sum.inl_injective
  have hn1:1≤Fintype.card V:=by omega
  have hW1:1≤Fintype.card (V⊕U):=by omega
  have hJ (ω:Ω):Fintype.card {u:U // u∉Z ω}≤(Fintype.card V)^2:=by
    have hh:Fintype.card {u:U // u∉Z ω}≤Fintype.card U:=Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    nlinarith
  have hI (ω:Ω):Fintype.card {v:V // v∉X ω}≤(Fintype.card (V⊕U))^2:=by
    have hh:Fintype.card {v:V // v∉X ω}≤Fintype.card V:=Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    nlinarith
  let Factor:Ω→(Sym2 (V⊕U)→Bool)→Prop:=fun ω σ=>∃hω:E ω,
    MixedFreshBoundaryAvoidingEvent p ρ ζ (Q ω) (F ω)
      (ordinaryPhysicalGraph (Q ω) (H ω)) (ordinaryPhysicalGraph (F ω) (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H₀ ω) (Z ω) (X ω))
      (fun i=>(ordinaryBoundaryRimSet (Q₀ ω) (X ω) i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet (H₀ ω) (X ω) (Z ω) i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) (data ω hω).endpoint_disjoint σ
  let Extra:Ω→(Sym2 (V⊕U)→Bool)→Prop:=fun ω σ=>Factor ω σ∧Other ω σ
  have hExtra:∀ω,E ω→1-(1/(Fintype.card V:ℝ)^q+δ)≤ν.probability (Extra ω):=by
    intro ω hω
    have hh:=hNf V (V⊕U) {u:U // u∉Z ω} {v:V // v∉X ω} (Sym2 (V⊕U))
      (by omega) (hJ ω) (hI ω) (Q ω) (F ω) (ordinaryPhysicalGraph (Q ω) (H ω))
      (ordinaryPhysicalGraph (F ω) (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet (H₀ ω) (Z ω) (X ω))
      (fun i=>(ordinaryBoundaryRimSet (Q₀ ω) (X ω) i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet (H₀ ω) (X ω) (Z ω) i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) (data ω hω)
    have hf:1-1/(Fintype.card V:ℝ)^q≤ν.probability (Factor ω):=by
      apply hh.trans
      apply finiteLaw_probability_mono
      intro σ hσ
      exact ⟨hω,hσ⟩
    have hi:=finiteLaw_good_intersection ν (Factor ω) (Other ω) δ (hOther ω hω)
    change _≤ν.probability (Extra ω) at hi
    linarith only [hf,hi]
  have hh:=hNr V U Ω (by omega) μ E e₀ hE Q₀ H₀ X Z p hp.le hp1 Extra
    (1/(Fintype.card V:ℝ)^q+δ) (by positivity) hExtra
  convert hh using 1 <;> try ring
end Oberwolfach
