module

public import Oberwolfach.MarkedReferenceChangedStatisticsCuts
public import Oberwolfach.MarkedReferenceChangedNeighbourhoods
public import Oberwolfach.MarkedCommonConfigurationsAfterHostChange
public import Oberwolfach.MarkedReferenceAgreementAfterPhysicalChange

@[expose] public section
/-! Seven common reference-level fields follow simultaneously from the
same original outcome and the same realized physical change graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_common_fields_after_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ) (g:Γ) (j:Color)
    (rho t gamma kappa D eps alphaOld gammaOld βA ξ ζ errR errI eOldR eOldC:ℝ)
    (hζ:0≤ζ) (hn:0<Fintype.card V) (q:U→Γ→ℝ) (s:U→Color→ℝ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hinterval:∀ e,σ (Sum.inr e)=τ (Sum.inr e))
    (hRim:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈FR.edgeFinset)
    (hSpoke:∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hdegR:∀ v,(FR.degree v:ℝ)≤ζ*Fintype.card V)
    (hdegS:∀ z,(FS.degree z:ℝ)≤ζ*Fintype.card V)
    (htypes:∀ v u,¬(H false v u∧H true v u))
    (herror:eps+ζ≤kappa/4) (halpha:2*gamma≤alphaOld)
    (hstep:2*ζ≤(3/2)*(gammaOld-2*gamma)*(rho*(r+4:ℝ)*t/2)^2)
    (hcut:∀ mark:Bool,ζ≤(alphaOld-2*gamma)*
      (if mark then (rho*(r+4:ℝ)*t/2)/(r+4:ℝ) else rho*(r+4:ℝ)*t/2)/4)
    (hbudgetR:errR+(r+12:ℝ)*(ζ*Fintype.card V+ζ*Fintype.card V)≤(kappa/4)*Fintype.card V)
    (hbudgetI:errI+(r+12:ℝ)*(ζ*Fintype.card V)≤(kappa/4)*Fintype.card V)
    (hbudgetC:ξ+4*ζ≤kappa/4)
    (hbudgetOldR:eOldR+ζ*Fintype.card V≤(kappa/4)*Fintype.card U)
    (hbudgetOldC:eOldC+ζ*Fintype.card V≤(kappa/4)*Fintype.card V):
    let p:=rho*(r+4:ℝ)*t/2
    let k:=p/(r+4:ℝ);
    MarkedReferenceStatistics P π d g j D eps kappa gammaOld p k ((r+4:ℝ)*t) t σ→
    MarkedReferenceCutFamilies P π d g j alphaOld p k t σ→
    MarkedRowsWithSpokes P π d (r+12) Finset.univ p k q s g j errR σ H→
    MarkedIndicesWithSpokes π d (r+12) Finset.univ q s g j errI σ H→
    MarkedCommonConfigurationsWithSpokes r P π d βA ξ σ H→
    (∀ b v,(∑ u,if ¬(rawMarkedPairSpokes π d σ g j b v u↔H b v u) then (1:ℝ) else 0)≤eOldR)→
    (∀ b u,(∑ v,if ¬(rawMarkedPairSpokes π d σ g j b v u↔H b v u) then (1:ℝ) else 0)≤eOldC)→
    MarkedReferenceStatistics P π d g j D (kappa/4) kappa (2*gamma) p k ((r+4:ℝ)*t) t τ ∧
    MarkedReferenceCutFamilies P π d g j (2*gamma) p k t τ ∧
    MarkedCommonConfigurationsWithSpokes r P π d βA (kappa/4) τ H' ∧
    MarkedRowsWithSpokes P π d (r+12) Finset.univ p k q s g j ((kappa/4)*Fintype.card V) τ H' ∧
    MarkedIndicesWithSpokes π d (r+12) Finset.univ q s g j ((kappa/4)*Fintype.card V) τ H' ∧
    (∀ b v,(∑ u,if ¬(rawMarkedPairSpokes π d τ g j b v u↔H' b v u) then (1:ℝ) else 0)≤(kappa/4)*Fintype.card U) ∧
    (∀ b u,(∑ v,if ¬(rawMarkedPairSpokes π d τ g j b v u↔H' b v u) then (1:ℝ) else 0)≤(kappa/4)*Fintype.card V) :=by
  intro p k hstats hcuts hrows hindices hconfig hOldR hOldC
  obtain ⟨hst,hcut'⟩:=marked_reference_changed_statistics_and_cuts P π d r g j rho t gamma kappa D eps alphaOld gammaOld ζ
    σ τ FR hinterval hRim hdegR hζ herror halpha hstep hcut hstats hcuts
  obtain ⟨hr,hi⟩:=marked_reference_changed_neighbourhoods P π d r rho t kappa ζ errR errI hζ q s g j
    σ τ H H' FR FS hrows hindices hRim hSpoke hdegR hdegS hbudgetR hbudgetI
  have hc:=marked_common_configurations_after_host_change r P π d βA ξ ζ hζ hn σ τ H H' FR FS hRim hSpoke hdegR hdegS htypes hconfig
  have hc':=marked_common_configurations_error_mono r P π d βA (ξ+4*ζ) (kappa/4) τ H' hbudgetC hc
  obtain ⟨hAgreeR,hAgreeC⟩:=marked_spoke_reference_agreement_after_physical_change π d σ τ g j H H' FS
    eOldR eOldC (ζ*Fintype.card V) hinterval hSpoke hOldR hOldC hdegS
  exact ⟨hst,hcut',hc',hr,hi,fun b v=>(hAgreeR b v).trans hbudgetOldR,
    fun b u=>(hAgreeC b u).trans hbudgetOldC⟩
end Oberwolfach
