module

public import Oberwolfach.OrdinarySelectedPostDemandTargetResult
public import Oberwolfach.OrdinarySelectedPostDemandOccupancyResult
public import Oberwolfach.OrdinaryPackageApproximateOccupied
public import Oberwolfach.OrdinaryPackageUnusedSpokesBound
public import Oberwolfach.OrdinaryLocalTargetsFitPlacementEventually
public import Oberwolfach.OrdinaryZeroRetentionPrior

@[expose] public section

/-! On the same selected matching and postmatching demand, retain the
strictly smaller uncovered-target bound needed for placement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 45000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem ordinary_selected_post_demand_local_target_eventually
    (ε c θ z a γ:ℝ) (hθ:0≤θ) (hz:0<z) (hε:ε≤c/16) (hzfloor:c*θ≤z)
    (ha:a≤z/16) (hγ:γ≤z/16):
    ∃N:ℕ,∀{n K:ℕ},N≤n→∀{U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F u).ConnectedComponent) (i₀:Fin K) (rsv lam:ℝ)
    (m d:ℕ) (π:Equiv.Perm (Fin n)) (P Del Target Protect Bad:SimpleGraph (Fin n))
    (Inner:Finset (Fin n)) (Hubs:Finset U) (bRate:ℝ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) tret)
    (q s:U→Bool→ℝ),
    (Inner.card:ℝ)≤ε*n→OrdinaryZeroRetentionEvent π d false σ→
    (∀w,1-(∑g,q w g)-(∑j,s w j)≤2*θ)→
    (∀w∈Hubs,|rawIntervalUnassignedHubCountOn π d (fun e=>σ (Sum.inr e)) w Inner-
      (Inner.card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<(Inner.card:ℝ)^(3/4:ℝ))→
    OrdinarySelectedPostDemandOccupancyResult F hF Cres i₀ rsv θ lam a γ m d π P Del Target Protect Bad Inner bRate σ tret Jret→
    OrdinarySelectedPostDemandTargetResult F hF Cres i₀ rsv θ lam a γ m d π P Del Target Protect Bad Inner Hubs bRate z σ tret Jret :=by
  obtain ⟨N,hfit⟩:=ordinary_local_targets_fit_placement_eventually ε c θ z a γ hθ hz hε hzfloor ha hγ
  refine ⟨N,?_⟩
  intro n K hn U _ _ F hF Cres i₀ rsv lam m d π P Del Target Protect Bad Inner Hubs bRate σ tret Jret q s
    hInner hzero hslack hlocal hpost
  unfold OrdinarySelectedPostDemandOccupancyResult at hpost
  unfold OrdinarySelectedPostDemandTargetResult
  obtain ⟨L,hL,hrows,hlocalRim,hmass,pk,hocc,hpack,hrest⟩:=hpost
  refine ⟨L,hL,hrows,hlocalRim,hmass,pk,hocc,hpack,?_,hrest⟩
  let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
  let rawI:RawIntervalFamilyOutcome (Fin n) U Bool Bool:=fun e=>raw (Sum.inr e)
  let raw':=rawMarkedDeleteRims raw Del.edgeFinset
  let Rim:=ordinaryShiftedPairRims (ordinaryEligibleHost P π d) π d raw'
  let H:=rawMarkedPairSpokes π d raw' true true
  let Old:=fun u=>(pk u).data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (pk u).inner
  let Image:=fun u=>(Old u).image (pk u).ψ
  have hFin:(fun (a b:Fin n)=>Classical.propDecidable (a=b))=instDecidableEqFin n:=Subsingleton.elim _ _
  have hno:∀w x,¬rawIntervalColouredStart π d (fun e=>rawI (w,e)) x false:=by
    have hh:=hzero.1
    rw [hFin] at hh
    simpa only [rawI,raw,rawExpandedApproximateCollapse,id_eq] using hh
  have hempty:∀u,IsEmpty (retainedMarkedIndex π d rawI false tret Jret u):=by
    have hgood:=hzero.2
    rw [hFin] at hgood
    have hh:=(hgood tret Jret 0 (by norm_num)).2
    convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  have happrox:∀w x,rawIntervalFamilyState π d rawI (x,w)=some (Sum.inl true)→x∈Image w:=by
    intro w x hx
    have hh:=ordinary_package_approximate_occupied π d m rawI w tret Jret _ _ _ _ _ _ _ _ (pk w) (hocc w)
    exact hh x hx
  have hrow:∀w∈Hubs,((ordinaryUnusedTrueSpokes π d rawI Image w).card:ℝ)≤(max a γ)*n:=by
    intro w hw
    letI:=hempty w
    have hh:=ordinary_package_unused_spokes_bound (K:=K) π d m Rim H L w _ _ _ _ _ _ (pk w)
    have hcard:((ordinaryUnusedTrueSpokes π d rawI Image w).card:ℝ)≤
        (((physicalSampledRow (ordinaryMixedPhysicalResource (U:=U) π)
          (typedMarkedResourceState Rim H) (ordinaryPhysicalRow (.inr (.inr w))))\
            L.biUnion (physicalSampledCandidateSet (ordinaryMixedPhysicalResource (U:=U) π) _ _)).card:ℝ):=by
      have heq:ordinaryUnusedTrueSpokes π d rawI Image w=
          (Finset.univ.filter (fun v=>H false v w))\Image w:=by
        ext v
        simp [ordinaryUnusedTrueSpokes,H,rawMarkedPairSpokes,rawMarkedSpokes,raw',rawMarkedDeleteRims,rawI]
        intro _
        congr! 10 <;> exact Subsingleton.elim _ _
      rw [heq]
      exact_mod_cast hh
    exact hcard.trans (hrows (.inr (.inr w)))
  have hlocal':∀w∈Hubs,|rawIntervalUnassignedHubCountOn π d rawI w Inner-
      (Inner.card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<(Inner.card:ℝ)^(3/4:ℝ):=by
    convert hlocal using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  have hb:=hfit n hn U π d rawI Inner Hubs Image q s hInner hno happrox hslack hlocal' hrow
  convert hb using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
