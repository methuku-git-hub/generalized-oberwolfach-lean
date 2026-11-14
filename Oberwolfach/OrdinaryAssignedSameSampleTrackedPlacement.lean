module

public import Oberwolfach.OrdinaryEarlyUniformTrackedPlacementAtRate
public import Oberwolfach.OrdinaryAssignedEventAllPlacementTests

@[expose] public section
/-! The common assigned event supplies the random inputs to the selected
uniform matching placement on exactly the same sample and reservoir. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem ordinary_assigned_same_sample_tracked_placement
    (d mMatch:ℕ) (hd:2≤d) (lam bList bRate εearly cBudget θ z aRow γrow ζlocal bMatch α δPlace ζret κcap ξedit:ℝ)
    (hRate:OrdinaryEarlyUniformTrackedPlacementAtRate d mMatch lam bList bRate εearly cBudget θ z aRow γrow ζlocal bMatch α δPlace ζret κcap ξedit):
    ∀(r m t a bAbs:ℕ),∃N:ℕ,∀n:ℕ,N≤n→2≤n→∀(qCount:ℕ)
    (P Host:SimpleGraph (Fin n)) (hHost:Host≤P) (π:Equiv.Perm (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)
    (A Wterm Inner:Finset (Fin n)) (Bterm B Hubs:Finset (Fin qCount)) (ξabs:ℝ)
    (γ pstar p smin rsv β ζ:ℝ) (s:(Fin qCount)→Bool→ℝ)
    (hγ:0≤γ) (hpstar:0≤pstar) (hp:pstar≤p) (hsmin:0≤smin) (hs:smin≤rsv)
    (hβ:0≤β) (hζ:0≤ζ) (hbζ:bList≤ζ)
    (hP:∀x,(1/2+γ)*n≤(P.degree x:ℝ))
    (herror:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n)
    (hmargin:β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*smin)
    (hlistBudget:lam+2*ζ≤β)
    ,
    let ε:ℝ:=min (lam/4) (bList/8)
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\Bad
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false;
    (Inner.card:ℝ)≤εearly*n→
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false);
    ∀{Kdim:ℕ} (F₀:(Fin qCount)→SimpleGraph (Fin n)) (hF₀:∀u,(F₀ u).IsRegularOfDegree 2)
      (Cres:∀u,Finset (F₀ u).ConnectedComponent) (i₀:Fin Kdim) (lamMatch:ℝ)
      (D:ℕ) (ρ₀:ℝ)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F₀ hF₀ Kdim i₀ rsv θ ((mMatch:ℝ)+1) ρ₀ smin d)
      (q₀:ℕ) (χlocal χglobal χhub χcol:ℝ)
      (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
      [∀τ,Fintype (R τ)] (ρ:∀τ,FiniteLaw (R τ))
      (ζevent χpair χlist χbal χbd χnbr χpairR χpath:ℝ)
      (σbal aEvent ζDel:ℝ)
      (w:∀i:Fin Kdim,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
      (seed:(Fin (mMatch+1)→Fin n)→ℝ) (tMatch ξMatch:ℝ)
      (extra:R σ) (coins:Sym2 (Fin n)→Bool)
      (hEvent:OrdinaryAssignedCorrectionEvent r d m a bAbs t q₀ n qCount Kdim D hd ζlocal χlocal χglobal χhub χcol ξabs
        P (permutationConflictGraph π (3*d)) π F₀ hF₀ i₀ rsv θ ρ₀ smin mMatch sampling
        A Inner Wterm Bterm B Hubs R ρ ζevent χpair χlist χbal χbd χnbr χpairR χpath
        Cres lamMatch aRow γrow σbal aEvent ζDel lam bMatch w seed tMatch ξMatch (⟨σ,extra⟩,coins)),
    let pActual:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F₀ hF₀ i₀ rsv θ ((mMatch:ℝ)+1) D
    let LF:ℝ:=2*((3*d:ℕ):ℝ);
    p=pActual → s=ordinaryAssignedSpokeProbability F₀ hF₀ Kdim i₀ rsv θ ((mMatch:ℝ)+1) →
    0<Kdim → 0<D → 0 ≤ rsv → rsv≤1/100 → 0<ρ₀ → ρ₀ ≤ initialIndexDensity (Fin qCount) D →
    initialIndexDensity (Fin qCount) D≤1 →
    ∀(S:Set ℕ),(∀u,AllowedCycleLengths (F₀ u) S)→OrdinaryClassReserveBound F₀ hF₀ i₀ rsv→
    (Fintype.card (Fin qCount) ≤ n) →
    (∀u (c:↥(Cres u)),Fintype.card c.val=i₀.val+1) →
    (∀u,((i₀.val+1:ℕ):ℝ)*(Cres u).card=rsv*n) →
    (∀x l,0<l → l<2*d+1 → (π^l) x≠x) →
    0≤ ζret → 0≤ lamMatch+γrow*(1-θ+lamMatch) → lamMatch+γrow*(1-θ+lamMatch)≤ θ/8 →
    max aRow γrow≤ κcap →
    1/(8*(d:ℝ))+((mMatch:ℝ)+1)*(d:ℝ)*ζret+(lamMatch+γrow*(1-θ+lamMatch))≤(δPlace/8)/2 →
    2*θ+δPlace/8+((mMatch:ℝ)+2)*κcap≤ δPlace →
    0<smin →
    let αCap:=5*ρ₀*smin^2/128;
    16/(d:ℝ)+16*κcap+16*bRate/αCap+4*z≤ θ/8 →
    ρ₀*n≤ 4*(Fintype.card (Fin qCount):ℝ) →
    (Hubs.card:ℝ)≤ αCap*n → (n:ℝ)^(3/4:ℝ)≤ αCap*n → bRate≤ αCap/16 → bRate≤ δPlace/8 →
    4/(d:ℝ)≤ δPlace/16 → 4*(n:ℝ)^(3/4:ℝ)≤ δPlace*n/16 →
    2*((max aRow γrow)*n)≤ δPlace*n/8 → (Hubs.card:ℝ)≤ δPlace*n/2 →
    lam/2≤ 1 → δPlace≤((lam/2)/100)^2 →
    100/(lam/2)≤(n:ℝ) → 2/Real.sqrt δPlace≤(n:ℝ) →
    ∃(Kabs:Finset (Sym2 (Fin n)⊕(Fin n×(Fin qCount)))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→(Fin qCount)→ Prop),
    OrdinaryCorrectedProtectedReservoirWitness r m t a bAbs ξabs Reference Bad Href A Inner Wterm Bterm B Kabs JQ JH ∧
    ∀Target:SimpleGraph (Fin n),
      (∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤ ξedit*n) →
      let Ref:=longPhysicalStateGraph P σ {0}\Bad;
      let Protect:=ordinaryMatchingProtect Ref Inner Kabs;
      OrdinarySelectedPostmatchingEmbeddingTrackedResult F₀ hF₀ Cres i₀ rsv θ lamMatch aRow γrow mMatch d π P
        (Sample\Target) Target Protect Sample Ref Bad σ 0 J Inner Hubs (ordinaryReservoirSpokeLabels Kabs) δPlace :=by
  intro r m t a bAbs
  obtain ⟨N,hN⟩:=hRate r m t a bAbs
  refine ⟨N,?_⟩
  intro n hn hn2 qCount P Host hHost π σ A Wterm Inner Bterm B Hubs ξabs γ pstar p smin rsv β ζ s
    hγ hpstar hp hsmin hs hβ hζ hbζ hP herror hmargin hlistBudget ε Sample Bad Reference Href hInner J
    Kdim F₀ hF₀ Cres i₀ lamMatch D ρ₀ sampling q₀ χlocal χglobal χhub χcol R _ ρ ζevent χpair χlist χbal χbd χnbr χpairR χpath
    σbal aEvent ζDel w seed tMatch ξMatch extra coins hEvent pActual p₂ LF hpEq hsEq
    hK hD hrs0 hrs1 hρ₀ hρlo hρhi Allowed hAllowed hClass hUn hsize hresSize hnoshort
    hζret hmatch0 hmatchUpper hκ hrate hsizeBudget hsminPos αCap hcapacity hUlo hHubs herrorCap hbα hbδ
    hDsmall hNsmall hRowRate hHubsδ hlam1 hδbound hnβ hnδ
  have hAll:=ordinary_assigned_event_all_placement_tests r d m a bAbs t q₀ n qCount Kdim D hd ζlocal χlocal χglobal χhub χcol ξabs
    P (permutationConflictGraph π (3*d)) π F₀ hF₀ i₀ rsv θ ρ₀ smin mMatch sampling A Inner Wterm Bterm B Hubs R ρ
    ζevent χpair χlist χbal χbd χnbr χpairR χpath Cres lamMatch aRow γrow σbal aEvent ζDel lam bMatch w seed tMatch ξMatch
    (⟨σ,extra⟩,coins) rfl hEvent
  obtain ⟨hres,hseq,hzero,hboundary,htests,hhub,hcolour,hfamily,hq,hcounts⟩:=hAll
  have hseq':∀w,s w false=rsv:=by simpa [hsEq] using hseq
  have htests':OrdinaryReservedCompletionTests P π d p smin s σ:=by simpa [hpEq,hsEq] using htests
  exact hN n hn hn2 qCount P Host hHost π σ A Inner Wterm Inner Bterm B Hubs ξabs γ pstar p smin rsv β ζ s
    hγ hpstar hp hsmin hs hseq' hβ hζ hbζ hP herror hmargin hlistBudget htests' hInner hres
    F₀ hF₀ Cres i₀ lamMatch D ρ₀ sampling hK hD hrs0 hrs1 hρ₀ hρlo hρhi Allowed hAllowed hClass
    hzero hhub hfamily hcolour hUn hsize hresSize hnoshort hζret hmatch0 hmatchUpper hκ hrate hsizeBudget hsminPos
    hcapacity hUlo hHubs herrorCap hbα hbδ hDsmall hNsmall hRowRate hHubsδ hlam1 hδbound hnβ hnδ
    hq hcounts hboundary htests
end Oberwolfach
