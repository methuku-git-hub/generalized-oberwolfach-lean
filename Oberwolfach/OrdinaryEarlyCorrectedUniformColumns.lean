module

public import Oberwolfach.OrdinaryEarlyCorrectedUniformTargets
public import Oberwolfach.OrdinaryUniformReservoirTargetColumns
public import Oberwolfach.OrdinaryCorrectedUniformTargetInputs
public import Oberwolfach.OrdinaryEarlyUniformEditSamplingBudget
public import Oberwolfach.OrdinaryUniformEditedTargetInputsFromOccupancy
public import Oberwolfach.OrdinarySelectedMatchingFamilyOccupancyForget
public import Oberwolfach.OrdinaryUniformEditsChosenCorrectedReservoir
public import Oberwolfach.OrdinaryUniformEditsSameSamplePostmatchingInputs
public import Oberwolfach.OrdinaryCorrectedReservoirNamedWitness

@[expose] public section

/-! A single corrected reservoir and a single deletion-uniform matching event
give the postmatching inputs for every admissible edit of that same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 45000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem ordinary_early_corrected_uniform_columns
    (r m t a bAbs d mMatch:ℕ) (lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch α:ℝ)
    (hlam:0<lam) (hbList:0<bList) (hbRate:0<bRate) (hbMatch:0<bMatch)
    (hmMatch:7≤mMatch) (hd:2≤d) (hda:1/θ≤d)
    (hθ:0<θ) (hθ1:θ≤1/100) (hz:0<z) (hδ:0<δplace) (hθδ:θ≤δplace/8)
    (hmatching:∀n:ℕ,2*((max aRow γrow)*n)≤δplace*n/8) (hεearly:εearly≤cBudget/16)
    (hεlist:εearly≤min (lam/4) (bList/8)) (hzfloor:cBudget*θ≤z)
    (ha:aRow≤z/16) (hγrow:γrow≤z/16) (haRate:aRow≤bRate/16) (hγθ:γrow≤θ)
    (hζlocal:0≤ζlocal) (hζθ:ζlocal≤θ) (hbLower:min (α/4096) (1/2:ℝ)*θ≤bRate)
    (hlocal:∀(n:ℕ) (inner θ' b a' γ' u t' edit del LF aux:ℝ),
      0 ≤ inner → 0 ≤ θ' → min (α/4096) (1/2:ℝ)*θ' ≤ b →
      inner ≤ εearly*n → a' ≤ b/16 → γ' ≤ θ' → u ≤ 2*θ' → t' ≤ θ'*inner →
      edit ≤ b*n/16 → aux ≤ b*n/16 → del ≤ b*n/16 → 2*LF ≤ b*n/16 →
      edit+(max (a'*n) (γ'*inner)+u*inner+3*t'+aux+del+LF)+LF ≤ b*n):
    ∃ξedit:ℝ,0<ξedit ∧ ξedit≤bList/8 ∧ ξedit≤bMatch ∧
    ∃N:ℕ,∀n:ℕ,N≤n→2≤n→∀(qCount:ℕ),qCount≤n→
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
    ∃(K:Finset (Sym2 (Fin n)⊕(Fin n×(Fin qCount)))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→(Fin qCount)→Prop),
    OrdinaryCorrectedProtectedReservoirWitness r m t a bAbs ξabs Reference Bad Href A Z Wterm Bterm B K JQ JH ∧
    ∀Target:SimpleGraph (Fin n),
    (∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤ξedit*n) →
    OrdinaryFixedPostmatchingColumnInputs F₀ hF₀ Cres i₀ rsv θ lamMatch aRow γrow mMatch d π P Target σ Inner Hubs K lam bRate z δplace :=by
  obtain ⟨ξedit,hξ,hξlist,hξmatch,N₁,hbase⟩:=ordinary_early_corrected_uniform_targets r m t a bAbs d mMatch
    lam bList bRate εearly cBudget θ z aRow γrow ζlocal bMatch α hlam hbList hbRate hbMatch hmMatch hd hda
    hθ hθ1 hz hεearly hεlist hzfloor ha hγrow haRate hγθ hζlocal hζθ hbLower hlocal
  obtain ⟨N₂,hcolumns⟩:=ordinary_uniform_reservoir_target_columns_eventually θ δplace aRow γrow hθ.le hδ hθδ
  refine ⟨ξedit,hξ,hξlist,hξmatch,max N₁ N₂,?_⟩
  intro n hn hn2 qCount hqCount P Host hHost π σ A Z Wterm Inner Bterm B Hubs ξabs γ pstar p smin rsv β ζ s
    hγ hpstar hp hsmin hs hseq hβ hζ hbζ hP herror hmargin hlistBudget hTests ε Sample Bad Reference Href
    hInnerEarly hRes J Kdim F₀ hF₀ Cres i₀ lamMatch D ρ₀ sampling pActual p₂ LF
    hK hD hrs0 hrs1 hρ₀ hρlo hρhi S hS hClass hzero hlocalHub hlocalCol hfamily hcolour
  have hprior:=hbase n (by omega) hn2 qCount P Host hHost π σ A Z Wterm Inner Bterm B Hubs ξabs γ pstar p smin rsv β ζ s
    hγ hpstar hp hsmin hs hseq hβ hζ hbζ hP herror hmargin hlistBudget hTests hInnerEarly hRes
    F₀ hF₀ Cres i₀ lamMatch D ρ₀ sampling hK hD hrs0 hrs1 hρ₀ hρlo hρhi S hS hClass hzero hlocalHub hfamily hcolour
  let q:=ordinaryAssignedMarkedProbability F₀ hF₀ Kdim θ ((mMatch:ℝ)+1)
  let s':=ordinaryAssignedSpokeProbability F₀ hF₀ Kdim i₀ rsv θ ((mMatch:ℝ)+1)
  have hc:8≤(mMatch:ℝ)+1:=by exact_mod_cast (show 8≤mMatch+1 by omega)
  have hslack:=ordinary_exact_assigned_hub_slack_upper (by omega) hD F₀ hF₀ Kdim hK i₀ rsv θ ((mMatch:ℝ)+1) d hd
    hrs0 hrs1 hθ hθ1 hc hda (hρ₀.trans_le hρlo) hρhi S hS hClass
  let Allowed:=fun Target:SimpleGraph (Fin n)=>
    ∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤ξedit*n
  let Witness:=fun K JQ JH=>OrdinaryCorrectedProtectedReservoirWitness r m t a bAbs ξabs Reference Bad Href A Z Wterm Bterm B K JQ JH
  exact hcolumns (by omega) (by simpa using hqCount) F₀ hF₀ Cres i₀ rsv lamMatch mMatch d π P σ Inner Hubs lam bRate z q s' Allowed Witness
    hzero hslack hlocalCol (hmatching n) hprior
end Oberwolfach
