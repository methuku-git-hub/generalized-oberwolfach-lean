module

public import Oberwolfach.OrdinaryAsymmetricPairingFromCleanupProbability
public import Oberwolfach.OrdinaryAsymmetricSameSampleRootFree
public import Oberwolfach.BoundaryReserveSupportEvent

@[expose] public section
/-! The actual cleanup profile supplies the asymmetric pairing and support
probabilities; their intersection with root-free cleanup yields one
protected cover-down on the same fresh physical sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_asymmetric_root_free_from_cleanup_profile
    (m:ℕ) (hm:3≤m) (γ b B p₀ κ:ℝ)
    (hγ:0<γ) (hb:0<b) (hB:0≤B) (hp₀:0<p₀) (hp₀1:p₀≤1) (hκ:0<κ) (hκ1:κ≤1):
    ∃ηhub ζhub a ηend ζlocal δend:ℝ,
      0<ηhub ∧ 0<ζhub ∧ 0<a ∧ a≤1 ∧ 0<ηend ∧ 0<ζlocal ∧ 0<δend ∧
    ∀(b₀ q:ℕ) (p ρ εsup:ℝ) (hp:0<p) (hp1:p≤1) (hρ:0<ρ) (hsup:0<εsup),∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
      (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
      (pR pH density tR tH Ledit βe₀ βh₀ βe βh η ell t ν budget deepBudget δsample:ℝ)
      (raw:RawWheelOutcome V U Γ Color),
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe₀ βh₀ s j raw→
    X.Nonempty→N≤X.card→Fintype.card {u:U // u∉Z}≤X.card^2→
    Fintype.card {v:V // v∉X}≤(ordinaryPhysicalInnerDomain X Z).card^2→
    γ*X.card≤βe₀*Fintype.card (V⊕U)→κ*X.card≤(Z.card:ℝ)→Z.card≤X.card→
    p₀≤pR→p₀≤pH→pH≤1→0≤tR→0≤tH→0≤Ledit→
    tR+Ledit≤δend*X.card→tH+Ledit≤δend*X.card→(∀v,F.degree v≤b₀)→
    OrdinaryMixedHubWeightsInnerScale m b B ηhub Q F H X Z→
    0≤t→Disjoint Q F→(∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)→
    βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)→η≤deepBudget→
    ∀(D:OrdinaryRootCoverData Q F H X T Z W (m+1) η ell),
    let Qfactor:=spanningRestriction Q X;
    let Hfactor:=fun v u=>H v u∧v∈X∧u∈Z;
    let n:ℝ:=(ordinaryPhysicalInnerDomain X Z).card;
    (∀σ (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W (m+1) η ell t ν D σ),
      BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ→
      OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample σ→
      OrdinaryGeneralRootFirstAsymmetricMargins m Q Qfactor F H Hfactor X T Z W η ell t ν D σ O
        p ρ ζhub ζlocal n εsup βe budget (p*ell+δsample*Fintype.card (V⊕U)))→
    ∀loss:ℝ,
    let μ:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-loss≤μ.probability (OrdinaryGeneralRootFreeSampledCoverCleanupSample m Q F H X T Z W η ell t ν D p βe βh δsample)→
    1-loss-1/(Fintype.card (V⊕U):ℝ)^q-(1/(X.card:ℝ)^q+1/(n:ℝ)^q)≤
      μ.probability (fun σ=>
        OrdinaryGeneralRootFreeSampledCoverCleanupSample m Q F H X T Z W η ell t ν D p βe βh δsample σ ∧
        BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ ∧
        MixedFreshPairingAsymmetricEvent m p ρ ζhub ζlocal n Qfactor F
          (ordinaryPhysicalGraph Qfactor Hfactor) (ordinaryPhysicalGraph F (fun _ _=>False))
          (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z X)
          (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl) (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)
          (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) σ ∧
        OrdinaryProtectedHostCoverDownResult Q F H X T Z W (m+1) budget deepBudget):=by
  obtain ⟨ηhub,ζhub,a,ηend,ζlocal,δend,hηhub,hζhub,ha,ha1,hηend,hζlocal,hδend,hpair⟩:=
    ordinary_asymmetric_pairing_from_cleanup_probability m hm γ b B p₀ κ hγ hb hB hp₀ hp₀1 hκ hκ1
  refine ⟨ηhub,ζhub,a,ηend,ζlocal,δend,hηhub,hζhub,ha,ha1,hηend,hζlocal,hδend,?_⟩
  intro b₀ q p ρ εsup hp hp1 hρ hsup
  obtain ⟨Np,hNp⟩:=hpair b₀ q p ρ hp hp1 hρ
  obtain ⟨Ns,hNs⟩:=boundary_reserve_support_high_probability εsup hsup q
  refine ⟨max Np Ns,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P Q F H X T Z W π d j s pR pH density tR tH Ledit βe₀ βh₀ βe βh
    η ell t ν budget deepBudget δsample raw profile hX hn hJ hI hscale hZX hZX' hpR hpH hpH1 htR htH hL
    hcostR hcostH hF data ht hQF hbal hdiv hmE hmH hdeep D Qfactor Hfactor n hnum loss μ hclean
  have hW:X.card≤Fintype.card (V⊕U):=
    (Finset.card_le_univ X).trans (Fintype.card_le_of_injective (Function.Embedding.inl:V↪V⊕U) Sum.inl_injective)
  have hpPair:=hNp V U Γ Color P Q F H X Z π d j s pR pH density tR tH Ledit βe₀ βh₀ raw
    profile hX (by omega) hJ hI hscale hZX hZX' hpR hpH hpH1 htR htH hL hcostR hcostH hF data
  have hpPair':1-(1/(X.card:ℝ)^q+1/(n:ℝ)^q)≤μ.probability
      (MixedFreshPairingAsymmetricEvent m p ρ ζhub ζlocal n Qfactor F
        (ordinaryPhysicalGraph Qfactor Hfactor) (ordinaryPhysicalGraph F (fun _ _=>False))
        (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z X)
        (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl) (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)
        (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val))):=by
    linarith only [hpPair]
  have hpSupport:=hNs (V⊕U) (by omega) (ordinaryBoundaryGraph Q H X Z) p hp.le hp1
  exact ordinary_asymmetric_same_sample_root_free m hm P Q Qfactor F H Hfactor π d X T Z W η ell t ν D
    pR pH p density tR tH Ledit βe₀ βh₀ βe βh ρ ζhub ζlocal n εsup budget deepBudget δsample s j raw
    ht hp.le hQF hbal hdiv profile hmE hmH hnum hdeep μ loss (1/(Fintype.card (V⊕U):ℝ)^q)
    (1/(X.card:ℝ)^q+1/(n:ℝ)^q) hclean hpSupport hpPair'
end Oberwolfach
