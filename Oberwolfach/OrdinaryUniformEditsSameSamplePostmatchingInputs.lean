module

public import Oberwolfach.OrdinaryOriginalSameSamplePostmatchingInputs

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

theorem ordinary_uniform_edits_same_sample_postmatching_inputs_eventually
    (r m t a bAbs d:ℕ) (lam bList bRate:ℝ)
    (hlam:0<lam) (hbList:0<bList) (hbRate:0<bRate):
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
    (Inner.card:ℝ)≤ε*n→ ξedit≤bList/8 → ξedit≤bMatch →
    ∀(K:Finset (Sym2 (Fin n)⊕(Fin n×(Fin qCount)))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→(Fin qCount)→Prop),
    OrdinaryCorrectedProtectedReservoirWitness r m t a bAbs ξabs Reference Bad Href A Z Wterm Bterm B K JQ JH→
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false);
    ∀{Kdim:ℕ} (mMatch:ℕ) (F₀:(Fin qCount)→SimpleGraph (Fin n)) (hF₀:∀u,(F₀ u).IsRegularOfDegree 2)
      (Cres:∀u,Finset (F₀ u).ConnectedComponent) (i₀:Fin Kdim) (θ lamMatch aRow γrow:ℝ)
      (D:ℕ) (ρ₀ ζlocal:ℝ)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F₀ hF₀ Kdim i₀ rsv θ ((mMatch:ℝ)+1) ρ₀ smin d),
    let pActual:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F₀ hF₀ i₀ rsv θ ((mMatch:ℝ)+1) D
    let LF:ℝ:=2*((3*d:ℕ):ℝ);
    OrdinaryZeroRetentionEvent π d false σ →
    (∀Del:SimpleGraph (Fin n), (∀v,(Del.degree v:ℝ)≤bMatch*n) →
      OrdinarySelectedMatchingFamilyLocalResult F₀ hF₀ Cres i₀ rsv θ lamMatch aRow γrow mMatch d π P Del Inner σ 0 J) →
    0≤ζlocal →
    (∀c:Fin 6,∀x∈Inner,
      |(((P.neighborFinset x∩Inner).filter (fun y=>(σ (Sum.inl s(x,y))).1=c)).card:ℝ)-
        markedExpandedPhysicalProbability pActual 0 p₂ 0 sampling.u c*(P.neighborFinset x∩Inner).card|≤ζlocal*Inner.card) →
    ξedit*n+(max (aRow*n) (γrow*Inner.card)+sampling.u*Inner.card+3*(ζlocal*Inner.card)+(6*d+4:ℕ)+ξedit*n+LF)+LF≤bRate*n →
    ∀Target:SimpleGraph (Fin n),
    (∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤ξedit*n) →
    OrdinaryFixedPostmatchingInputs F₀ hF₀ Cres i₀ rsv θ lamMatch aRow γrow mMatch d π P Target σ Inner Hubs K lam bRate :=by
  obtain ⟨N,hbase⟩:=ordinary_original_same_sample_postmatching_inputs_eventually r m t a bAbs d lam bList bRate hlam hbList hbRate
  refine ⟨N,?_⟩
  intro n hn hn2 qCount P Host hHost π σ A Z Wterm Inner Bterm B Hubs ξabs γ pstar p smin rsv β ζ ξedit bMatch s
    hγ hpstar hp hsmin hs hseq hβ hζ hbζ hP herror hmargin hlistBudget hTests ε Sample Bad Reference Href
    hInner hEditList hEditMatch K JQ JH hW J Kdim mMatch F₀ hF₀ Cres i₀ θ lamMatch aRow γrow D ρ₀ ζlocal
    sampling pActual p₂ LF hzero hfamily hζlocal hcolour hbudget Target hEdit
  have hDel:∀v,((Sample\Target).degree v:ℝ)≤bMatch*n:=by
    have hlost:=lost_graph_degree_le_symmetric_edit Target Sample (ξedit*n) hEdit
    intro v
    have hh : ξedit*n ≤ bMatch*n := by gcongr
    have hv := (hlost v).trans hh
    convert hv using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  have hedit : ξedit*n ≤ (bList/8)*n := by gcongr
  apply hbase n hn hn2 qCount P Target Host hHost π σ A Z Wterm Inner Bterm B Hubs ξabs
    γ pstar p smin rsv β ζ (ξedit*n) s hγ hpstar hp hsmin hs hseq hβ hζ hbζ hP herror hmargin hlistBudget hTests
    (fun _=>∅) (by intro u; simp) hInner hEdit hedit K JQ JH hW mMatch F₀ hF₀ Cres i₀ θ lamMatch aRow γrow
    D ρ₀ ζlocal sampling hzero ?_ hζlocal hcolour hbudget
  apply hfamily (Sample\Target)
  intro v
  convert hDel v using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
