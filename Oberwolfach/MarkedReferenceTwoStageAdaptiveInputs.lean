module

public import Oberwolfach.MarkedReferenceTwoStageInputs
public import Oberwolfach.MarkedModifiedPhysicalIncidence
public import Oberwolfach.MarkedLocalConfigurationsAfterHostChange
public import Oberwolfach.MarkedLocalSpokeLoadSharedChanges

@[expose] public section
/-! One parent-level sample supplies the two-stage inputs uniformly after
all physical changes satisfying the displayed degree and error budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}
theorem marked_reference_two_stage_inputs_after_changes
    (L:MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (eps₁ eps₂ θ pstar ζ:ℝ) (hreg:kappa≤eps₂) (hζ:0≤ζ) (hpstar:0<pstar) (hB:0≤BA):
    letI:Fintype L.VP:=L.inst7
    letI:Fintype L.UP:=L.inst8
    letI:LinearOrder L.VP:=L.inst9
    letI:DecidableEq L.UP:=L.inst10
    let n:ℝ:=Fintype.card L.VP
    let p:=rho*(r+4:ℝ)*t/2
    let k:=rho*t/2
    let sr:=(r+4:ℝ)*t
    let D:=2*Fintype.card L.UP/rho;
    0<Fintype.card L.VP→
    pstar≤p→pstar≤k→pstar≤sr→p≤1→k≤1→sr≤1→
    (kappa/4)*n+(r+12:ℝ)*(ζ*n+ζ*n)≤min eps₁ eps₂*n→
    (kappa/4)*n+(r+12:ℝ)*(ζ*n)≤min eps₁ eps₂*n→
    2*β≤3*min betaA (t/4)-(r+5:ℝ)*(ζ+ζ)→
    2*β≤3*min betaA (t/4)-(r+7:ℝ)*ζ-(r+4:ℝ)*ζ→
    thetaDeep/4+15*((r+4:ℝ)+1)^4*(2*BA/pstar^(2*(r+4)+1))*ζ≤θ/2→
    ∀ (τ:RawMarkedOutcome L.VP L.UP Gamma Color) (H':Bool→L.VP→L.UP→Prop)
      (FR:SimpleGraph L.VP) (FS:SimpleGraph (L.VP⊕L.UP)),
    (∀ e,¬(rawMarkedPairRims L.PP L.πP d L.σBase e↔rawMarkedPairRims L.PP L.πP d τ e)→markedPairPhysical L.πP e∈FR.edgeFinset)→
    (∀ b v u,¬(L.HBase b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
    (∀ b v u,H' b v u→L.HBase b v u)→
    (∀ v,(FR.degree v:ℝ)≤ζ*n)→(∀ z,(FS.degree z:ℝ)≤ζ*n)→
    (∀ v,|(L.PP.degree v:ℝ)-D|≤eps₂*n) ∧
    (∀ u,L.qP u L.aP=t) ∧ (∀ u,L.sP u L.cP=sr) ∧
    MarkedRowsWithSpokes L.PP L.πP d (r+12) Finset.univ p k L.qP L.sP L.aP L.cP
      (min eps₁ eps₂*n) τ H' ∧
    MarkedIndicesWithSpokes L.πP d (r+12) Finset.univ L.qP L.sP L.aP L.cP
      (min eps₁ eps₂*n) τ H' ∧
    SuccessorSequenceWeightConditions L.PP L.πP (3*d) D L.tauRef aLoA BA L.weightRef ∧
    MarkedLocalConfigurationsWithSpokes r L.PP L.πP d Finset.univ (2*β) (2*β) τ H' ∧
    MarkedLocalSpokeLoadsWithSpokes L.PP L.πP d (r+4) D p k sr L.weightRef (θ/2) τ H' ∧
    (∀ v u,¬(H' false v u∧H' true v u)) ∧
    (∀ u v z,H' false v u→H' true z u→v≠L.πP z):=by
  letI:Fintype L.VP:=L.inst7
  letI:Fintype L.UP:=L.inst8
  letI:LinearOrder L.VP:=L.inst9
  letI:DecidableEq L.UP:=L.inst10
  intro n p k sr D hn hp hk hs hp1 hk1 hs1 hbudgetR hbudgetI hC hP hbudgetLoad τ H' FR FS hRim hSpoke hsub hdegR hdegS
  have hkr:rho*(r+4:ℝ)*t/2/(r+4:ℝ)=rho*t/2:=by field_simp
  have hnonneg:0≤ζ*n:=mul_nonneg hζ (Nat.cast_nonneg _)
  have hneigh:=marked_neighbourhoods_after_physical_change L.PP L.πP d (r+12) Finset.univ Finset.univ
    p k L.qP L.sP L.aP L.cP ((kappa/4)*n) ((kappa/4)*n) (ζ*n) (ζ*n) (ζ*n) hnonneg hnonneg hnonneg
    L.σBase τ L.HBase H' (by simpa only [p,k,hkr] using L.hrowsP0) L.hindicesP0 FR FS hRim hSpoke hdegR
    (fun v=>hdegS (Sum.inl v)) (fun u=>hdegS (Sum.inr u))
  have hrows:=marked_rows_with_spokes_tolerance_mono L.PP L.πP d (r+12) Finset.univ p k L.qP L.sP L.aP L.cP _ _ τ H'
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hbudgetR) hneigh.1
  have hindices:=marked_indices_with_spokes_tolerance_mono L.πP d (r+12) Finset.univ L.qP L.sP L.aP L.cP _ _ τ H'
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hbudgetI) hneigh.2
  have hcfg:=marked_local_configurations_after_host_change r L.PP L.πP d _ _ ζ L.σBase τ L.HBase H' FR FS
    hRim hSpoke hdegR hdegS (fun v u=>L.hdtypesBase u v) L.hDeepConfigs0
  have hcfg':=marked_local_configurations_with_spokes_mono r L.PP L.πP d Finset.univ _ _ (2*β) (2*β) τ H'
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hC) (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hP) hcfg
  have hload:=marked_local_spoke_loads_from_shared_changes L.PP L.πP d (r+4) (by omega) hn D L.tauRef aLoA BA
    L.hDloP L.hDhiP p k sr pstar hpstar hp hk hs hp1 hk1 hs1 hB L.weightRef L.hwRef (thetaDeep/4) ζ (θ/2) hζ
    L.σBase τ L.HBase H' (by simpa only [D,p,k,sr,hkr] using L.hDeepLoad0) FR FS hRim hSpoke hdegR hdegS
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hbudgetLoad)
  have hn0:0≤(Fintype.card L.VP:ℝ):=Nat.cast_nonneg _
  refine ⟨fun v=>(L.hPreg v).trans (mul_le_mul_of_nonneg_right hreg hn0),L.hqP,L.hsP,hrows,hindices,L.hwRef,hcfg',hload,?_,?_⟩
  · intro v u hh
    exact L.hdtypesBase u v ⟨hsub false v u hh.1,hsub true v u hh.2⟩
  · intro u v z hv hz
    exact L.hsepBase u v z (hsub false v u hv) (hsub true z u hz)
end Oberwolfach
