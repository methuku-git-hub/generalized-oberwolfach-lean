module

public import Oberwolfach.OrdinarySelectedPostmatchingDemandOccupancy
public import Oberwolfach.OrdinaryAssignedVortexExactSamplingData
public import Oberwolfach.OrdinaryEmptyRetentionOutcome
public import Oberwolfach.OrdinaryMatchingProtectChoice
public import Oberwolfach.OrdinaryLostEdgesEditDegree

@[expose] public section
/-! On the original assigned sample, the locally tested matching and the
edited-target demand use the same zero-retention package family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem ordinary_original_postmatching_demand_occupancy
    {n q K D:ℕ} (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F u).ConnectedComponent) (i₀:Fin K) (rsv θ ρ₀ smin lam a γ:ℝ)
    (m d:ℕ) (π:Equiv.Perm (Fin n)) (P Target:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (bRate ζ edit:ℝ)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d):
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=longPhysicalStateGraph P σ {0}\Bad
    let Protect:=ordinaryMatchingProtect Reference Inner Kabs
    let Del:=Sample\Target
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)
    let p:=initialIndexDensity (Fin q) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((m:ℝ)+1) D
    let t:=ζ*Inner.card
    let LF:ℝ:=2*((3*d:ℕ):ℝ);
    OrdinaryZeroRetentionEvent π d false σ →
    OrdinarySelectedMatchingFamilyLocalOccupancyResult F hF Cres i₀ rsv θ lam a γ m d π P Del Inner σ 0 J →
    0≤ζ →
    (∀c:Fin 6,∀x∈Inner,
      |(((P.neighborFinset x∩Inner).filter (fun y=>(σ (Sum.inl s(x,y))).1=c)).card:ℝ)-
        markedExpandedPhysicalProbability p 0 p₂ 0 sampling.u c*(P.neighborFinset x∩Inner).card|≤t) →
    (∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤edit) →
    edit+(max (a*n) (γ*Inner.card)+sampling.u*Inner.card+3*t+(6*d+4:ℕ)+edit+LF)+LF≤bRate*n →
    OrdinarySelectedPostDemandOccupancyResult F hF Cres i₀ rsv θ lam a γ m d π
      P Del Target Protect Bad Inner bRate σ 0 J :=by
  intro Sample Bad Reference Protect Del J p p₂ t LF hzero hfamily hζ hcolour hEdit hBudget
  have hret:=ordinary_zero_retention_event_empty_outcome π d false σ hzero 0 (by norm_num)
  have hempty:∀u,IsEmpty (retainedMarkedIndex π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σ (Sum.inr e))) false 0 J u):=by
    convert hret.2 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  have hDel:∀x,(Del.degree x:ℝ)≤edit:=by
    have hh:=lost_graph_degree_le_symmetric_edit Target Sample edit hEdit
    intro x
    convert hh x using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  have hBad:∀x,(Bad.degree x:ℝ)≤LF:=by
    intro x
    have hh:=permutationConflictGraph_degree_le π (3*d) x
    dsimp [Bad,LF]
    exact_mod_cast hh
  have hProtect:Protect≤Reference:=(ordinary_matching_protect_choice Reference Inner Kabs).1
  have ht:0≤t:=by dsimp [t];positivity
  have hsum:2*p+2*p₂+sampling.u≤1:=by
    have hh:=sampling.hsum
    change 2*p+2*0+2*p₂+2*0+sampling.u≤1 at hh
    linarith
  exact ordinary_selected_postmatching_demand_occupancy F hF Cres i₀ rsv θ lam a γ m d π P Del Target Protect Bad Inner bRate σ 0 J
    hempty hfamily p p₂ sampling.u t edit LF edit sampling.hp sampling.hp₂ sampling.hu ht hsum hcolour
    (by intro x; convert hDel x using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    hBad hProtect hEdit hBudget
end Oberwolfach
