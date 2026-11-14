module

public import Oberwolfach.OrdinaryAdaptiveFreshPairingFromCleanup
public import Oberwolfach.OrdinaryCleanupProfileLocalEvents

@[expose] public section
/-! Extend a prior common outcome carrying an actual cleanup profile and
    general-length hub weights to fresh pairings, reserves and support on
    one further physical-edge sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 14000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_fresh_pairing_cleanup_local_events
    (m b₀:ℕ) (hm:3≤m) (γ κ b Bweight p₀ a:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤Bweight) (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (q:ℕ)
      (εres εsup βe βh:ℝ) (hres:0<εres) (hsup:0<εsup) (hβe:0<βe) (hβh:0<βh),∃N:ℕ,
    ∀(V U Ω Γ Color:Type) [Fintype V] [Fintype U] [Fintype Ω] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e₀:ℝ),1-e₀≤μ.probability E→
    ∀(P Q₀ F:Ω→SimpleGraph V) (H₀:Ω→V→U→Prop) (X:Ω→Finset V) (Z:Ω→Finset U)
      (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ) (raw:Ω→RawWheelOutcome V U Γ Color)
      (pR pH density tR tH L:ℝ),
    (∀ω,E ω→OrdinaryCleanupParentProfiles (P ω) (Q₀ ω) (F ω) (H₀ ω) π d (X ω) (Z ω)
      pR pH density tR tH L βe βh s j (raw ω))→
    (∀ω,E ω→(X ω).Nonempty)→p₀≤pH→pH≤1→
    γ*Fintype.card V≤βe*Fintype.card (V⊕U)→κ*Fintype.card V≤βe*Fintype.card (V⊕U)→
    (∀ω,E ω→∀v,((F ω).degree v:ℝ)≤ε*Fintype.card V)→
    (∀ω,E ω→∀w:V⊕U,(ordinaryPhysicalGraph (F ω) (fun _ _=>False)).degree w≤b₀)→
    (∀ω,E ω→a*Fintype.card (V⊕U)+tR+L≤pR*density*(X ω).card)→
    (∀ω,E ω→a*Fintype.card (V⊕U)+tH+L≤pH*(Z ω).card)→
    (∀ω,E ω→∀x,(tH+2*L)+pH*(tH+L)≤η*((Z ω).filter (H₀ ω x)).card)→
    (∀ω,E ω→∀x,(tR+2*L)+pH*(tR+L)≤η*((X ω)∩(Q₀ ω).neighborFinset x).card)→
    (∀ω,E ω→∀x,(tH+3*L)+pH^2*(tH+L)≤η*((Z ω).filter (H₀ ω x)).card)→
    (∀ω,E ω→Nonempty (OrdinaryMixedHubWeightsOfLength m b Bweight η (Q₀ ω) (F ω) (H₀ ω) (X ω) (Z ω)))→
    let Q:=fun ω=>spanningRestriction (Q₀ ω) (X ω);
    let H:=fun ω v u=>H₀ ω v u∧v∈X ω∧u∈Z ω;
    let ν:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-(e₀+4/(Fintype.card (V⊕U):ℝ)^q+1/(Fintype.card V:ℝ)^q)≤
      (μ.sigma (fun _=>ν)).probability (fun z=>E z.1 ∧
        OrdinaryBoundaryReserveGood (Q₀ z.1) (H₀ z.1) (X z.1) (Z z.1) p εres z.2 ∧
        BoundaryReserveSupportGood (ordinaryBoundaryGraph (Q₀ z.1) (H₀ z.1) (X z.1) (Z z.1)) p εsup z.2 ∧
        MixedFreshPairingAvoidingEvent m p ρ ζ (Q z.1) (F z.1)
          (ordinaryPhysicalGraph (Q z.1) (H z.1)) (ordinaryPhysicalGraph (F z.1) (fun _ _=>False))
          (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H₀ z.1) (Z z.1) (X z.1))
          (fun i=>(ordinaryBoundaryRimSet (Q₀ z.1) (X z.1) i).image Sum.inl)
          (fun i=>(ordinaryBoundaryRowSet (H₀ z.1) (X z.1) (Z z.1) i).image Sum.inr)
          (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) z.2 ∧
        OrdinaryBoundaryExtensionGood (Q₀ z.1) (H₀ z.1) (X z.1) βe p z.2 ∧
        OrdinaryBoundaryHubPairGood (H₀ z.1) (Z z.1) βh p z.2):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hbase⟩:=ordinary_adaptive_fresh_pairing_from_cleanup m b₀ hm
    γ κ b Bweight p₀ a hγ hκ hb hB hp₀ hp₀1 ha ha1
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 ρ hρ q εres εsup βe βh hres hsup hβe hβh
  obtain ⟨Nm,hNm⟩:=hbase p hp hp1 ρ hρ q εres εsup hres hsup
  obtain ⟨Nl,hNl⟩:=ordinary_cleanup_profile_boundary_local_probability βe βh p hβe hβh hp hp1 q
  refine ⟨max Nm Nl,?_⟩
  intro V U Ω Γ Color _ _ _ _ _ _ _ hn hU μ E e₀ hE P Q₀ F H₀ X Z π d j s raw
    pR pH density tR tH L hprofile hA hpH hpH1 hγscale hκscale hF hFphys hRbudget hHbudget hrow hcol hcodeg hweight
    Q H ν
  have hnW:Fintype.card V≤Fintype.card (V⊕U):=Fintype.card_le_of_injective Sum.inl Sum.inl_injective
  let Other:Ω→(Sym2 (V⊕U)→Bool)→Prop:=fun ω σ=>
    OrdinaryBoundaryExtensionGood (Q₀ ω) (H₀ ω) (X ω) βe p σ ∧
      OrdinaryBoundaryHubPairGood (H₀ ω) (Z ω) βh p σ
  have hOther:∀ω,E ω→1-2/(Fintype.card (V⊕U):ℝ)^q≤ν.probability (Other ω):=by
    intro ω hω
    exact hNl V U Γ Color (by omega) (P ω) (Q₀ ω) (F ω) (H₀ ω) π d (X ω) (Z ω)
      pR pH density tR tH L s j (raw ω) (hprofile ω hω)
  have hh:=hNm V U Ω Γ Color (by omega) hU μ E e₀ hE P Q₀ F H₀ X Z π d j s raw
    pR pH density tR tH L βe βh hprofile hA hpH hpH1 hγscale hκscale hF hFphys hRbudget hHbudget
    hrow hcol hcodeg hweight Other (2/(Fintype.card (V⊕U):ℝ)^q) (by positivity) hOther
  convert hh using 1 <;> try ring
end Oberwolfach
