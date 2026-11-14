module

public import Oberwolfach.OrdinaryEarlyUniformColumnsAtRate
public import Oberwolfach.OrdinaryUniformColumnEmbedding

@[expose] public section
/-! The selected column callback gives tracked embeddings for every edit at
its original rate, without bounding the entire hub set by the placement error. -/
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

theorem ordinary_uniform_column_tracked_placement_at_rate
    (d mMatch:ℕ) (hm:7≤mMatch) (hd:2≤d)
    (lam bList bRate εearly cBudget θ z δPlace aRow γrow ζlocal bMatch α ζret κcap ξedit:ℝ)
    (hθ:0<θ) (hθ1:θ≤1/100) (hδ:0<δPlace) (hlam:0<lam) (hbRate:0≤bRate)
    (hcolumns:OrdinaryEarlyUniformColumnsAtRate d mMatch lam bList bRate εearly cBudget θ z δPlace aRow γrow ζlocal bMatch α ξedit):
    ∀(r m t a bAbs:ℕ),∃N:ℕ,∀n:ℕ,N≤n→2≤n→∀(qCount:ℕ),qCount≤n→
    ∀(P Host:SimpleGraph (Fin n)) (hHost:Host≤P) (π:Equiv.Perm (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)
    (A Z Wterm Inner:Finset (Fin n)) (Bterm B Hubs:Finset (Fin qCount)) (ξabs:ℝ)
    (γ pstar p smin rsv β ζ:ℝ) (s:(Fin qCount)→Bool→ℝ)
    (hγ:0≤γ) (hpstar:0≤pstar) (hp:pstar≤p) (hsmin:0≤smin) (hs:smin≤rsv)
    (hseq:∀w,s w false=rsv) (hβ:0≤β) (hζ:0≤ζ) (hbζ:bList≤ζ)
    (hP:∀x,(1/2+γ)*n≤(P.degree x:ℝ))
    (herror:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n)
    (hmargin:β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*smin)
    (hlistBudget:lam+2*ζ≤β)
    (hTests:OrdinaryReservedCompletionTests P π d p smin s σ),
    let ε:ℝ:=min (lam/4) (bList/8)
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\Bad
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false;
    (Inner.card:ℝ)≤εearly*n→
    OrdinaryCorrectedProtectedReservoir r m t a bAbs ξabs Reference Bad Href A Z Wterm Bterm B →
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false);
    ∀{Kdim:ℕ} (F₀:(Fin qCount)→SimpleGraph (Fin n)) (hF₀:∀u,(F₀ u).IsRegularOfDegree 2)
      (Cres:∀u,Finset (F₀ u).ConnectedComponent) (i₀:Fin Kdim) (lamMatch:ℝ)
      (D:ℕ) (ρ₀:ℝ)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F₀ hF₀ Kdim i₀ rsv θ ((mMatch:ℝ)+1) ρ₀ smin d),
    let pActual:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F₀ hF₀ i₀ rsv θ ((mMatch:ℝ)+1) D
    let LF:ℝ:=2*((3*d:ℕ):ℝ);
    0<Kdim → 0<D → 0 ≤ rsv → rsv≤1/100 → 0<ρ₀ → ρ₀ ≤ initialIndexDensity (Fin qCount) D →
    initialIndexDensity (Fin qCount) D≤1 →
    ∀(S:Set ℕ),(∀u,AllowedCycleLengths (F₀ u) S)→OrdinaryClassReserveBound F₀ hF₀ i₀ rsv→
    OrdinaryZeroRetentionEvent π d false σ →
    (∀w∈Hubs,|rawIntervalUnassignedHubCountOn π d (fun e=>σ (Sum.inr e)) w Inner-
      (Inner.card:ℝ)*(1-(∑g,ordinaryAssignedMarkedProbability F₀ hF₀ Kdim θ ((mMatch:ℝ)+1) w g)-
        (∑j,ordinaryAssignedSpokeProbability F₀ hF₀ Kdim i₀ rsv θ ((mMatch:ℝ)+1) w j))|<(Inner.card:ℝ)^(3/4:ℝ)) →
    (∀v∈Inner,|rawIntervalUnassignedColumnCount π d (fun e=>σ (Sum.inr e)) v Hubs-
      ∑w∈Hubs,(1-(∑g,ordinaryAssignedMarkedProbability F₀ hF₀ Kdim θ ((mMatch:ℝ)+1) w g)-
        (∑j,ordinaryAssignedSpokeProbability F₀ hF₀ Kdim i₀ rsv θ ((mMatch:ℝ)+1) w j))|<(Inner.card:ℝ)^(3/4:ℝ)) →
    (∀Del:SimpleGraph (Fin n), (∀v,(Del.degree v:ℝ)≤bMatch*n) →
      OrdinarySelectedMatchingFamilyLocalOccupancyResult F₀ hF₀ Cres i₀ rsv θ lamMatch aRow γrow mMatch d π P Del Inner σ 0 J) →
    (∀c:Fin 6,∀x∈Inner,
      |(((P.neighborFinset x∩Inner).filter (fun y=>(σ (Sum.inl s(x,y))).1=c)).card:ℝ)-
        markedExpandedPhysicalProbability pActual 0 p₂ 0 sampling.u c*(P.neighborFinset x∩Inner).card|≤ζlocal*Inner.card) →
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
    2*((max aRow γrow)*n)≤ δPlace*n/8 →
    lam/2≤ 1 → δPlace≤((lam/2)/100)^2 →
    100/(lam/2)≤(n:ℝ) → 2/Real.sqrt δPlace≤(n:ℝ) →
    (∀u,(∑g:Bool,ordinaryAssignedMarkedProbability F₀ hF₀ Kdim θ ((mMatch:ℝ)+1) u g)≤ 1/8) →
    (∀u g,|rawIntervalHubStartCount π d g (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σ (Sum.inr e))) u-
      (n:ℝ)*ordinaryAssignedMarkedProbability F₀ hF₀ Kdim θ ((mMatch:ℝ)+1) u g/d|<(n:ℝ)^(3/4:ℝ)/d) →
    OrdinaryBoundaryStartEvent π d σ →
    OrdinaryReservedCompletionTests P π d pActual smin
      (ordinaryAssignedSpokeProbability F₀ hF₀ Kdim i₀ rsv θ ((mMatch:ℝ)+1)) σ →
    ∃(Kabs:Finset (Sym2 (Fin n)⊕(Fin n×(Fin qCount)))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→(Fin qCount)→ Prop),
    OrdinaryCorrectedProtectedReservoirWitness r m t a bAbs ξabs Reference Bad Href A Z Wterm Bterm B Kabs JQ JH ∧
    ∀Target:SimpleGraph (Fin n),
      (∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤ ξedit*n) →
      let Ref:=longPhysicalStateGraph P σ {0}\Bad;
      let Protect:=ordinaryMatchingProtect Ref Inner Kabs;
      OrdinarySelectedPostmatchingEmbeddingTrackedResult F₀ hF₀ Cres i₀ rsv θ lamMatch aRow γrow mMatch d π P
        (Sample\Target) Target Protect Sample Ref Bad σ 0 J Inner Hubs (ordinaryReservoirSpokeLabels Kabs) δPlace :=by
  obtain ⟨Nembed,hembed⟩:=ordinary_uniform_column_embedding_eventually mMatch d hm hd θ δPlace hθ hδ
  intro r m t a bAbs
  obtain ⟨Ncol,hbase⟩:=hcolumns r m t a bAbs
  refine ⟨max Ncol Nembed,?_⟩
  intro n hn hn2 qCount hqCount P Host hHost π σ A Z Wterm Inner Bterm B Hubs ξabs γ pstar p smin rsv β ζ s
    hγ hpstar hp hsmin hs hseq hβ hζ hbζ hP herror hmargin hlistBudget hTests ε Sample Bad Reference Href
    hInner hRes J Kdim F₀ hF₀ Cres i₀ lamMatch D ρ₀ sampling pActual p₂ LF
    hK hD hrs0 hrs1 hρ₀ hρlo hρhi Allowed hAllowed hClass hzero hhub hcol hfamily hcolour
    hUn hsize hres hnoshort hζret hmatch0 hmatchUpper hκ hrate hsizeBudget hsminPos αCap
    hcapacity hUlo hHubs herrorCap hbα hbδ hDsmall hNsmall hRowRate hlam1 hδbound
    hnβ hnδ hq hcounts hboundary htestsActual
  obtain ⟨Kabs,JQ,JH,hw,htarget⟩:=hbase n (by omega) hn2 qCount hqCount P Host hHost π σ A Z Wterm Inner Bterm B Hubs ξabs
    γ pstar p smin rsv β ζ s hγ hpstar hp hsmin hs hseq hβ hζ hbζ hP herror hmargin hlistBudget hTests
    hInner hRes F₀ hF₀ Cres i₀ lamMatch D ρ₀ sampling hK hD hrs0 hrs1 hρ₀ hρlo hρhi Allowed hAllowed hClass
    hzero hhub hcol hfamily hcolour
  refine ⟨Kabs,JQ,JH,hw,?_⟩
  intro Target hEdit Ref Protect
  exact hembed (n:=n) (K:=Kdim) (by omega) (by omega) hK (Fin qCount) hUn F₀ hF₀ Allowed hAllowed
    i₀ rsv hrs0 hrs1 hθ1 hClass Cres hsize hres π hnoshort P σ Inner Hubs Kabs lamMatch aRow γrow ζret κcap
    bRate z ρ₀ smin lam pActual hζret hmatch0 hmatchUpper hκ hrate hsizeBudget hρ₀ hsminPos hbRate
    hcapacity hUlo hHubs herrorCap hbα hbδ hDsmall hNsmall hRowRate hlam hlam1 hδbound hnβ hnδ
    hq hcounts hzero hboundary (ordinaryAssignedSpokeProbability F₀ hF₀ Kdim i₀ rsv θ ((mMatch:ℝ)+1)) htestsActual
    (fun T=>∀v,((Finset.univ.filter (fun w=>Xor (T.Adj v w) (Sample.Adj v w))).card:ℝ)≤ξedit*n) htarget Target hEdit
end Oberwolfach
