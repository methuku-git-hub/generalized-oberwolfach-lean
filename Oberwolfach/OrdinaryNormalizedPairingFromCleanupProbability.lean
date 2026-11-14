module

public import Oberwolfach.OrdinaryNormalizedHubProbabilityFromCleanup
public import Oberwolfach.OrdinaryLocalEndpointFromCleanupProbability
public import Oberwolfach.OrdinaryNormalizedMixedPairingSameSample
public import Oberwolfach.OrdinaryPhysicalRimInside

@[expose] public section
/-! The same fresh physical sample supplies both hub factors and endpoint
pairings for a fixed cleanup profile and its selected inner-scale weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_normalized_pairing_from_cleanup_probability
    (m:ℕ) (hm:3≤m) (γ b B p₀ κ:ℝ)
    (hγ:0<γ) (hb:0<b) (hB:0≤B) (hp₀:0<p₀) (hp₀1:p₀≤1) (hκ:0<κ) (hκ1:κ≤1):
    ∃ηhub ζhub a ηend ζlocal δend:ℝ,
      0<ηhub ∧ 0<ζhub ∧ 0<a ∧ a≤1 ∧ 0<ηend ∧ 0<ζlocal ∧ 0<δend ∧
    ∀(b₀ q:ℕ) (p ρ:ℝ) (hp:0<p) (hp1:p≤1) (hρ:0<ρ),∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
      (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
      (pR pH density tR tH L βe βh:ℝ) (σ:RawWheelOutcome V U Γ Color),
    OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH L βe βh s j σ→
    A.Nonempty→N≤A.card→Fintype.card {u:U // u∉Z}≤A.card^2→
    Fintype.card {v:V // v∉A}≤(ordinaryPhysicalInnerDomain A Z).card^2→
    γ*A.card≤βe*Fintype.card (V⊕U)→κ*A.card≤(Z.card:ℝ)→Z.card≤A.card→
    p₀≤pR→p₀≤pH→pH≤1→0≤tR→0≤tH→0≤L→
    tR+L≤δend*A.card→tH+L≤δend*A.card→(∀v,F.degree v≤b₀)→
    OrdinaryMixedHubWeightsInnerScale m b B ηhub Q F H A Z→
    ∀ζ ζambient:ℝ,ζ≤ζhub→ζ≤ζambient→
    ζambient*Fintype.card (V⊕U)≤ζlocal*(ordinaryPhysicalInnerDomain A Z).card→
    let S:=fun i:{v:V // v∉A}=>(ordinaryBoundaryRimSet Q A i).image (Sum.inl:V→V⊕U);
    let R:=fun i:{v:V // v∉A}=>(ordinaryBoundaryRowSet H A Z i).image (Sum.inr:U→V⊕U);
    let G:=ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z);
    let K:=ordinaryPhysicalGraph F (fun _ _=>False);
    let g:=fun i:{v:V // v∉A}=>physicalIncidentCoin (Sum.inl i.val:V⊕U);
    1-1/(A.card:ℝ)^q-1/((ordinaryPhysicalInnerDomain A Z).card:ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
      (MixedFreshPairingAvoidingEvent m p ρ ζ (spanningRestriction Q A) F G K
        (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z A) S R
        (fun h=>hubSpokeCoin h.val) g):=by
  obtain ⟨ηhub,ζhub,hηhub,hζhub,hhub⟩:=ordinary_normalized_hub_probability_from_cleanup m hm γ b B hγ hb hB
  obtain ⟨a,ηend,ζlocal,δend,ha,ha1,hηend,hζlocal,hδend,hend⟩:=
    ordinary_local_endpoint_from_cleanup_probability p₀ κ hp₀ hp₀1 hκ hκ1
  refine ⟨ηhub,ζhub,a,ηend,ζlocal,δend,hηhub,hζhub,ha,ha1,hηend,hζlocal,hδend,?_⟩
  intro b₀ q p ρ hp hp1 hρ
  obtain ⟨Nh,hNh⟩:=hhub b₀ q p hp hp1
  obtain ⟨Ne,hNe⟩:=hend b₀ q p hp hp1
  obtain ⟨Ns,hNs⟩:=ordinary_normalized_mixed_pairing_same_sample m ρ hρ
  refine ⟨max Nh (max Ne Ns),?_⟩
  intro V U Γ Color _ _ _ _ _ _ P Q F H A Z π d j s pR pH density tR tH L βe βh σ profile
    hA hn hJ hI hscale hZA hZA' hpR hpH hpH1 htR htH hL hcostR hcostH hF data ζ ζambient hζh hζe hζscale
    S R G K g
  have hAc:0<A.card:=Finset.card_pos.mpr hA
  have hinner:A.card≤(ordinaryPhysicalInnerDomain A Z).card:=by
    rw [ordinary_physical_inner_domain_card];omega
  have hamb:A.card≤Fintype.card (V⊕U):=
    (Finset.card_le_univ A).trans (Fintype.card_le_of_injective (Function.Embedding.inl:V↪V⊕U) Sum.inl_injective)
  have ph:=hNh V U Γ Color P Q F H A Z π d j s pR pH density tR tH L βe βh σ
    profile hA (by omega) hJ hscale hF data
  have pe:=hNe V U Γ Color P Q F H A Z π d j s pR pH density tR tH L βe βh σ
    profile hA (by omega) hI hZA hZA' hpR hpH hpH1 htR htH hL hcostR hcostH hF
  have hmap:(spanningRestriction Q A).map (Function.Embedding.inl:V↪V⊕U)≤G:=
    ordinary_physical_rim_inside (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z)
  exact hNs V U {v:V // v∉A} (by omega) Q F H A Z G K (ordinaryPhysicalInnerDomain A Z) S R g
    p ζ ζhub ζlocal ζambient hp hp1 hζh hζe hζscale hmap (1/(A.card:ℝ)^q)
    (1/((ordinaryPhysicalInnerDomain A Z).card:ℝ)^q) ph pe
end Oberwolfach
