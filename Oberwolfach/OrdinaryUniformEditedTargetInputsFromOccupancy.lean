module

public import Oberwolfach.OrdinaryOriginalPostDemandLocalTargets
public import Oberwolfach.OrdinaryOriginalPostmatchingDemandOccupancy
public import Oberwolfach.OrdinaryFixedPostmatchingTargetInputsMerge
public import Oberwolfach.OrdinaryLostEdgesEditDegree

@[expose] public section

/-! One fixed sample, reservoir and local event provide the refined
placement inputs for every admissible edited target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem ordinary_uniform_edited_target_inputs_from_occupancy
    (ε cBudget θ z a γ:ℝ) (hθ:0<θ) (hθ1:θ≤1/100) (hz:0<z)
    (hε:ε≤cBudget/16) (hzfloor:cBudget*θ≤z) (ha:a≤z/16) (hγ:γ≤z/16):
    ∃N:ℕ,∀{n qCount K D:ℕ},N≤n→0<n→0<K→0<D→
    ∀(F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F u).ConnectedComponent) (i₀:Fin K) (rsv ρ₀ smin lam:ℝ)
    (m d:ℕ),7≤m → 2≤d → 0 ≤ rsv → rsv≤1/100 → 1/θ≤d →
    0 < initialIndexDensity (Fin qCount) D→initialIndexDensity (Fin qCount) D≤1→
    ∀(S:Set ℕ),(∀u,AllowedCycleLengths (F u) S)→OrdinaryClassReserveBound F hF i₀ rsv→
    ∀(π:Equiv.Perm (Fin n)) (P:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin qCount))
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin qCount))) (lamList bRate ζ ξedit bMatch:ℝ)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d),
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)
    let q:=ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1)
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1)
    let p:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((m:ℝ)+1) D
    let LF:ℝ:=2*((3*d:ℕ):ℝ);
    (Inner.card:ℝ)≤ε*n→ξedit≤bMatch→0≤ζ→OrdinaryZeroRetentionEvent π d false σ→
    (∀w∈Hubs,|rawIntervalUnassignedHubCountOn π d (fun e=>σ (Sum.inr e)) w Inner-
      (Inner.card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<(Inner.card:ℝ)^(3/4:ℝ))→
    (∀c:Fin 6,∀x∈Inner,
      |(((P.neighborFinset x∩Inner).filter (fun y=>(σ (Sum.inl s(x,y))).1=c)).card:ℝ)-
        markedExpandedPhysicalProbability p 0 p₂ 0 sampling.u c*(P.neighborFinset x∩Inner).card|≤ζ*Inner.card)→
    (∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤bMatch*n)→
      OrdinarySelectedMatchingFamilyLocalOccupancyResult F hF Cres i₀ rsv θ lam a γ m d π P Del Inner σ 0 J)→
    ξedit*n+(max (a*n) (γ*Inner.card)+sampling.u*Inner.card+3*(ζ*Inner.card)+(6*d+4:ℕ)+ξedit*n+LF)+LF≤bRate*n→
    (∀Target:SimpleGraph (Fin n),
      (∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤ξedit*n)→
      OrdinaryFixedPostmatchingInputs F hF Cres i₀ rsv θ lam a γ m d π P Target σ Inner Hubs Kabs lamList bRate)→
    ∀Target:SimpleGraph (Fin n),
      (∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤ξedit*n)→
      OrdinaryFixedPostmatchingTargetInputs F hF Cres i₀ rsv θ lam a γ m d π P Target σ Inner Hubs Kabs lamList bRate z :=by
  obtain ⟨N,hbound⟩:=ordinary_original_post_demand_local_targets_eventually ε cBudget θ z a γ hθ hθ1 hz hε hzfloor ha hγ
  refine ⟨N,?_⟩
  intro n qCount K D hn hn0 hK hD F hF Cres i₀ rsv ρ₀ smin lam m d hm hd hs0 hs1 hda hρ hρ1 S hS hClass
    π P σ Inner Hubs Kabs lamList bRate ζ ξedit bMatch sampling Sample J q s p p₂ LF
    hInner hEditMatch hζ hzero hlocal hcolour hfamily hbudget hbase Target hEdit
  have hDel:∀v,((Sample\Target).degree v:ℝ)≤bMatch*n:=by
    have hh:=lost_graph_degree_le_symmetric_edit Target Sample (ξedit*n) hEdit
    have he:ξedit*n≤bMatch*n:=by gcongr
    intro v
    convert (hh v).trans he using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  have hfam:=hfamily (Sample\Target) (by
    intro v
    convert hDel v using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
  have hpost:=ordinary_original_postmatching_demand_occupancy F hF Cres i₀ rsv θ ρ₀ smin lam a γ m d π P Target σ
    Inner Kabs bRate ζ (ξedit*n) sampling hzero hfam hζ hcolour hEdit hbudget
  let Bad:=permutationConflictGraph π (3*d)
  let Reference:=longPhysicalStateGraph P σ {0}\Bad
  let Protect:=ordinaryMatchingProtect Reference Inner Kabs
  have htarget:=hbound hn hn0 hK hD F hF Cres i₀ rsv lam m d hm hd hs0 hs1 hda hρ hρ1 S hS hClass
    π P (Sample\Target) Target Protect Bad Inner Hubs bRate σ 0 J hInner hzero hlocal hpost
  exact ordinary_fixed_postmatching_target_inputs_merge F hF Cres i₀ rsv θ lam a γ m d π P Target σ Inner Hubs Kabs
    lamList bRate z (hbase Target hEdit) htarget
end Oberwolfach
