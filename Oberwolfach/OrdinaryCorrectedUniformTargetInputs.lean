module

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

theorem ordinary_corrected_uniform_target_inputs_eventually
    (r m t a bAbs d:ℕ) (lam bList bRate εearly cBudget θ z aRow γrow:ℝ)
    (hlam:0<lam) (hbList:0<bList) (hbRate:0<bRate)
    (hθ:0<θ) (hθ1:θ≤1/100) (hz:0<z) (hεearly:εearly≤cBudget/16)
    (hzfloor:cBudget*θ≤z) (ha:aRow≤z/16) (hγrow:γrow≤z/16):
    ∃N:ℕ,∀n:ℕ,N≤n→2≤n→∀(qCount:ℕ)
    (P Host:SimpleGraph (Fin n)) (hHost:Host≤P) (π:Equiv.Perm (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)
    (A Z Wterm Inner:Finset (Fin n)) (Bterm B Hubs:Finset (Fin qCount)) (ξabs:ℝ)
    (γ pstar p smin rsv β ζ ξedit bMatch:ℝ) (s:(Fin qCount)→Bool→ℝ)
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
    (Inner.card:ℝ)≤ε*n→ (Inner.card:ℝ)≤εearly*n→ ξedit≤bList/8 → ξedit≤bMatch →
    OrdinaryCorrectedProtectedReservoir r m t a bAbs ξabs Reference Bad Href A Z Wterm Bterm B →
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false);
    ∀{Kdim:ℕ} (mMatch:ℕ) (F₀:(Fin qCount)→SimpleGraph (Fin n)) (hF₀:∀u,(F₀ u).IsRegularOfDegree 2)
      (Cres:∀u,Finset (F₀ u).ConnectedComponent) (i₀:Fin Kdim) (lamMatch:ℝ)
      (D:ℕ) (ρ₀ ζlocal:ℝ)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F₀ hF₀ Kdim i₀ rsv θ ((mMatch:ℝ)+1) ρ₀ smin d),
    let pActual:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F₀ hF₀ i₀ rsv θ ((mMatch:ℝ)+1) D
    let LF:ℝ:=2*((3*d:ℕ):ℝ);
    0<Kdim → 0<D → 7≤mMatch → 2≤d → 0 ≤ rsv → rsv≤1/100 → 1/θ≤d →
    0 < initialIndexDensity (Fin qCount) D → initialIndexDensity (Fin qCount) D≤1 →
    ∀(S:Set ℕ),(∀u,AllowedCycleLengths (F₀ u) S)→OrdinaryClassReserveBound F₀ hF₀ i₀ rsv→
    OrdinaryZeroRetentionEvent π d false σ →
    (∀w∈Hubs,|rawIntervalUnassignedHubCountOn π d (fun e=>σ (Sum.inr e)) w Inner-
      (Inner.card:ℝ)*(1-(∑g,ordinaryAssignedMarkedProbability F₀ hF₀ Kdim θ ((mMatch:ℝ)+1) w g)-
        (∑j,ordinaryAssignedSpokeProbability F₀ hF₀ Kdim i₀ rsv θ ((mMatch:ℝ)+1) w j))|<(Inner.card:ℝ)^(3/4:ℝ)) →
    (∀Del:SimpleGraph (Fin n), (∀v,(Del.degree v:ℝ)≤bMatch*n) →
      OrdinarySelectedMatchingFamilyLocalOccupancyResult F₀ hF₀ Cres i₀ rsv θ lamMatch aRow γrow mMatch d π P Del Inner σ 0 J) →
    0≤ζlocal →
    (∀c:Fin 6,∀x∈Inner,
      |(((P.neighborFinset x∩Inner).filter (fun y=>(σ (Sum.inl s(x,y))).1=c)).card:ℝ)-
        markedExpandedPhysicalProbability pActual 0 p₂ 0 sampling.u c*(P.neighborFinset x∩Inner).card|≤ζlocal*Inner.card) →
    ξedit*n+(max (aRow*n) (γrow*Inner.card)+sampling.u*Inner.card+3*(ζlocal*Inner.card)+(6*d+4:ℕ)+ξedit*n+LF)+LF≤bRate*n →
    ∃(K:Finset (Sym2 (Fin n)⊕(Fin n×(Fin qCount)))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→(Fin qCount)→Prop),
    OrdinaryCorrectedProtectedReservoirWitness r m t a bAbs ξabs Reference Bad Href A Z Wterm Bterm B K JQ JH ∧
    ∀Target:SimpleGraph (Fin n),
    (∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤ξedit*n) →
    OrdinaryFixedPostmatchingTargetInputs F₀ hF₀ Cres i₀ rsv θ lamMatch aRow γrow mMatch d π P Target σ Inner Hubs K lam bRate z :=by
  obtain ⟨N₁,hbase⟩:=ordinary_uniform_edits_chosen_corrected_reservoir_eventually r m t a bAbs d lam bList bRate hlam hbList hbRate
  obtain ⟨N₂,htarget⟩:=ordinary_uniform_edited_target_inputs_from_occupancy εearly cBudget θ z aRow γrow
    hθ hθ1 hz hεearly hzfloor ha hγrow
  refine ⟨max N₁ N₂,?_⟩
  intro n hn hn2 qCount P Host hHost π σ A Z Wterm Inner Bterm B Hubs ξabs γ pstar p smin rsv β ζ ξedit bMatch s
    hγ hpstar hp hsmin hs hseq hβ hζ hbζ hP herror hmargin hlistBudget hTests ε Sample Bad Reference Href
    hInner hInnerEarly hEditList hEditMatch hRes J Kdim mMatch F₀ hF₀ Cres i₀ lamMatch D ρ₀ ζlocal
    sampling pActual p₂ LF hK hD hmMatch hd hrs0 hrs1 hda hρ hρ1 S hS hClass hzero hlocalHub hfamily hζlocal hcolour hbudget
  have hfamilyOld:∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤bMatch*n)→
      OrdinarySelectedMatchingFamilyLocalResult F₀ hF₀ Cres i₀ rsv θ lamMatch aRow γrow mMatch d π P Del Inner σ 0 J:=by
    intro Del hDel
    exact ordinary_selected_matching_family_occupancy_forget F₀ hF₀ Cres i₀ rsv θ lamMatch aRow γrow mMatch d π P Del Inner σ 0 J (hfamily Del hDel)
  obtain ⟨K,JQ,JH,hW,hfixed⟩:=hbase n (by omega) hn2 qCount P Host hHost π σ A Z Wterm Inner Bterm B Hubs ξabs γ pstar p smin rsv β ζ ξedit bMatch s
    hγ hpstar hp hsmin hs hseq hβ hζ hbζ hP herror hmargin hlistBudget hTests hInner hEditList hEditMatch hRes
    mMatch F₀ hF₀ Cres i₀ θ lamMatch aRow γrow D ρ₀ ζlocal sampling hzero hfamilyOld hζlocal hcolour hbudget
  refine ⟨K,JQ,JH,hW,?_⟩
  exact htarget (by omega) (by omega) hK hD F₀ hF₀ Cres i₀ rsv ρ₀ smin lamMatch mMatch d hmMatch hd hrs0 hrs1 hda hρ hρ1 S hS hClass
    π P σ Inner Hubs K lam bRate ζlocal ξedit bMatch sampling hInnerEarly hEditMatch hζlocal hzero hlocalHub hcolour hfamily hbudget hfixed
end Oberwolfach
