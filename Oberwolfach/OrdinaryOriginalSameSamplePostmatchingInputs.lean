module

public import Oberwolfach.OrdinaryFixedPostmatchingInputsFromReservoir
public import Oberwolfach.OrdinaryOriginalSelectedPostmatchingFromSample
public import Oberwolfach.OrdinaryFixedReservoirSeparateListBudgets
public import Oberwolfach.OrdinaryFixedPostmatchingInputsFromEdit
public import Oberwolfach.OrdinaryFixedCorrectedReservoirLabelBudgets
public import Oberwolfach.OrdinaryCorrectedReservoirLabelBudgets
public import Oberwolfach.OrdinaryReservedActualTargetLists
public import Oberwolfach.OrdinaryReservedActualTargetAvoidance

@[expose] public section
/-! The same sample's corrected reservoir and selected reserved-list tests
supply actual edited-target deletion, assignment and list inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_same_sample_postmatching_inputs_eventually
    (r m t a bAbs d:ℕ) (lam bList bRate:ℝ) (hlam:0<lam) (hbList:0<bList) (hbRate:0<bRate):
    ∃N:ℕ,∀n:ℕ,N≤n→2≤n→∀(qCount:ℕ)
    (P Target Host:SimpleGraph (Fin n)) (hHost:Host≤P) (π:Equiv.Perm (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)
    (A Z Wterm Inner:Finset (Fin n)) (Bterm B Hubs:Finset (Fin qCount)) (ξ:ℝ)
    (γ pstar p smin rsv β ζ edit:ℝ) (s:(Fin qCount)→Bool→ℝ)
    (hγ:0≤γ) (hpstar:0≤pstar) (hp:pstar≤p) (hsmin:0≤smin) (hs:smin≤rsv)
    (hseq:∀w,s w false=rsv) (hβ:0≤β) (hζ:0≤ζ) (hbζ:bList≤ζ)
    (hP:∀x,(1/2+γ)*n≤(P.degree x:ℝ))
    (herror:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n)
    (hmargin:β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*smin)
    (hlistBudget:lam+2*ζ≤β)
    (hTests:OrdinaryReservedCompletionTests P π d p smin s σ)
    (Old:(Fin qCount)→Finset (Fin n)) (hOld:∀u,Disjoint (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u) (Old u)),
    let ε:ℝ:=min (lam/4) (bList/8)
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let F:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\F
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false;
    (Inner.card:ℝ)≤ε*n→
    (∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤edit)→
    edit≤(bList/8)*n→
    ∀(K:Finset (Sym2 (Fin n)⊕(Fin n×(Fin qCount)))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→(Fin qCount)→Prop),
    OrdinaryCorrectedProtectedReservoirWitness r m t a bAbs ξ Reference F Href A Z Wterm Bterm B K JQ JH→
    let Ref0:=longPhysicalStateGraph P σ {0}\F
    let Protect0:=ordinaryMatchingProtect Ref0 Inner K
    let DelMatch:=Sample\Target
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false);
    ∀{Kdim:ℕ} (mMatch:ℕ) (F₀:(Fin qCount)→SimpleGraph (Fin n)) (hF₀:∀u,(F₀ u).IsRegularOfDegree 2)
      (Cres:∀u,Finset (F₀ u).ConnectedComponent) (i₀:Fin Kdim) (θ lamMatch aRow γrow:ℝ),
    ∀(D:ℕ) (ρ₀ ζlocal:ℝ)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F₀ hF₀ Kdim i₀ rsv θ ((mMatch:ℝ)+1) ρ₀ smin d),
    let pActual:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F₀ hF₀ i₀ rsv θ ((mMatch:ℝ)+1) D
    let LF:ℝ:=2*((3*d:ℕ):ℝ);
    OrdinaryZeroRetentionEvent π d false σ →
    OrdinarySelectedMatchingFamilyLocalResult F₀ hF₀ Cres i₀ rsv θ lamMatch aRow γrow mMatch d π
      P DelMatch Inner σ 0 J →
    0≤ζlocal →
    (∀c:Fin 6,∀x∈Inner,
      |(((P.neighborFinset x∩Inner).filter (fun y=>(σ (Sum.inl s(x,y))).1=c)).card:ℝ)-
        markedExpandedPhysicalProbability pActual 0 p₂ 0 sampling.u c*(P.neighborFinset x∩Inner).card|≤ζlocal*Inner.card) →
    edit+(max (aRow*n) (γrow*Inner.card)+sampling.u*Inner.card+3*(ζlocal*Inner.card)+(6*d+4:ℕ)+edit+LF)+LF≤bRate*n →
    OrdinaryFixedPostmatchingInputs F₀ hF₀ Cres i₀ rsv θ lamMatch aRow γrow mMatch d π P Target σ Inner Hubs K lam bRate :=by
  obtain ⟨N,hbase⟩:=ordinary_fixed_postmatching_inputs_from_reservoir_eventually r m t a bAbs d lam bList bRate hlam hbList hbRate
  refine ⟨N,?_⟩
  intro n hn hn2 qCount P Target Host hHost π σ A Z Wterm Inner Bterm B Hubs ξ γ pstar p smin rsv β ζ edit s
    hγ hpstar hp hsmin hs hseq hβ hζ hbζ hP herror hmargin hlistBudget hTests Old hOld ε Sample F Reference Href
    hInner hEdit hedit K JQ JH hW Ref0 Protect0 DelMatch J Kdim mMatch F₀ hF₀ Cres i₀ θ lamMatch aRow γrow
    D ρ₀ ζlocal sampling pActual p₂ LF hzero hfamily hζlocal hcolour hbudget
  have hpost:=ordinary_original_selected_postmatching_from_sample F₀ hF₀ Cres i₀ rsv θ ρ₀ smin lamMatch aRow γrow
    mMatch d π P Target σ Inner K bRate ζlocal edit sampling hzero hfamily hζlocal hcolour hEdit hbudget
  exact hbase n hn hn2 (Fin qCount) P Target Host hHost π σ A Z Wterm Inner Bterm B Hubs ξ γ pstar p smin rsv β ζ edit s
    hγ hpstar hp hsmin hs hseq hβ hζ hbζ hP herror hmargin hlistBudget hTests Old hOld hInner hEdit hedit K JQ JH hW
    mMatch F₀ hF₀ Cres i₀ θ lamMatch aRow γrow hpost
end Oberwolfach
