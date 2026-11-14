module

public import Oberwolfach.OrdinarySelectedPostDemandOccupancyResult
public import Oberwolfach.OrdinarySelectedMatchingFamilyLocalOccupancyResult
public import Oberwolfach.OrdinaryActualLocalPostmatchingDemand
public import Oberwolfach.OrdinaryZeroRetainedFamilyOldHost

@[expose] public section
/-! Select the actual demand after the locally tested matching family. The
old edges, local coverage and placement budget belong to that same family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem ordinary_selected_postmatching_demand_occupancy {n q K:ℕ}
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F u).ConnectedComponent) (i₀:Fin K) (rsv θ lam a γ:ℝ)
    (m d:ℕ) (π:Equiv.Perm (Fin n)) (P Del Target Protect Bad:SimpleGraph (Fin n))
    (Inner:Finset (Fin n)) (bRate:ℝ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) tret)
    (hempty:∀u,IsEmpty (retainedMarkedIndex π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σ (Sum.inr e))) false tret Jret u))
    (hfamily:OrdinarySelectedMatchingFamilyLocalOccupancyResult F hF Cres i₀ rsv θ lam a γ m d π P Del Inner σ tret Jret)
    (p p₂ u t δ LF edit:ℝ) (hp:0≤p) (hp₂:0≤p₂) (hu:0≤u) (ht:0≤t)
    (hsum:2*p+2*p₂+u≤1)
    (hcolour:∀c:Fin 6,∀x∈Inner,
      |(((P.neighborFinset x∩Inner).filter (fun y=>(σ (Sum.inl s(x,y))).1=c)).card:ℝ)-
        markedExpandedPhysicalProbability p 0 p₂ 0 u c*(P.neighborFinset x∩Inner).card|≤t)
    (hDel:∀x,(Del.degree x:ℝ)≤δ) (hBad:∀x,(Bad.degree x:ℝ)≤LF)
    (hProtect:Protect≤longPhysicalStateGraph P σ {0}\Bad)
    (hEdit:∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) ((longPhysicalStateGraph P σ {0,1,2,3,4}).Adj v w))).card:ℝ)≤edit)
    (hBudget:edit+(max (a*n) (γ*Inner.card)+u*Inner.card+3*t+(6*d+4:ℕ)+δ+LF)+LF≤bRate*n):
    OrdinarySelectedPostDemandOccupancyResult F hF Cres i₀ rsv θ lam a γ m d π P Del Target Protect Bad Inner bRate σ tret Jret :=by
  unfold OrdinarySelectedMatchingFamilyLocalOccupancyResult at hfamily
  unfold OrdinarySelectedPostDemandOccupancyResult
  obtain ⟨L,hL,hrows,hlocal,hmass,pk,hocc,hpack⟩:=hfamily
  refine ⟨L,hL,hrows,hlocal,hmass,pk,hocc,hpack,?_⟩
  intro Old Sample Reference Used Required
  have hHost:ordinaryEligibleHost P π d≤P:=by intro x y h;exact h.1
  have hOld:=ordinary_zero_retained_family_old_host _ m d π _ P (ordinaryEligibleHost P π d) Del Bad hHost σ
    _ _ _ _ _ _ pk hempty
  have hActual:=ordinary_actual_local_postmatching_demand (K:=K) Old P Del Bad Inner π d m σ Target Protect edit
    p 0 p₂ 0 u t δ (max (a*n) (γ*Inner.card)) LF hp (by norm_num) hp₂ (by norm_num) hu
    (by linarith) ht hcolour hDel hBad hOld.1 hOld.2 hProtect hEdit L (fun v=>(pk v).marker)
    (fun v=>(pk v).hGood) (fun v edge he=>(pk v).hAllRims edge he) hlocal
  obtain ⟨hG,hdis,hRef,hOldG,hGdeg,hcoverage⟩:=hActual
  refine ⟨hG,hdis,hRef,hOldG,?_,hcoverage⟩
  intro v
  have hh:=hGdeg v
  norm_num at hh hBudget
  exact hh.trans hBudget
end Oberwolfach
