module

public import Oberwolfach.MarkedReferenceTwoStageAdaptiveInputs
public import Oberwolfach.MarkedRawStateChange
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
theorem marked_reference_two_stage_inputs_after_deletions
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
    ∀ (FR:SimpleGraph L.VP) (FS:SimpleGraph (L.VP⊕L.UP)),
    (∀ v,(FR.degree v:ℝ)≤ζ*n)→(∀ z,(FS.degree z:ℝ)≤ζ*n)→
    let σ':=rawMarkedDeleteRims L.σBase FR.edgeFinset
    let H':=markedDeletePhysicalSpokes L.HBase FS;
    (∀ v,|(L.PP.degree v:ℝ)-D|≤eps₂*n) ∧
    (∀ u,L.qP u L.aP=t) ∧ (∀ u,L.sP u L.cP=sr) ∧
    MarkedRowsWithSpokes L.PP L.πP d (r+12) Finset.univ p k L.qP L.sP L.aP L.cP
      (min eps₁ eps₂*n) σ' H' ∧
    MarkedIndicesWithSpokes L.πP d (r+12) Finset.univ L.qP L.sP L.aP L.cP
      (min eps₁ eps₂*n) σ' H' ∧
    SuccessorSequenceWeightConditions L.PP L.πP (3*d) D L.tauRef aLoA BA L.weightRef ∧
    MarkedLocalConfigurationsWithSpokes r L.PP L.πP d Finset.univ (2*β) (2*β) σ' H' ∧
    MarkedLocalSpokeLoadsWithSpokes L.PP L.πP d (r+4) D p k sr L.weightRef (θ/2) σ' H' ∧
    (∀ v u,¬(H' false v u∧H' true v u)) ∧
    (∀ u v z,H' false v u→H' true z u→v≠L.πP z) :=by
  letI:Fintype L.VP:=L.inst7
  letI:Fintype L.UP:=L.inst8
  letI:LinearOrder L.VP:=L.inst9
  letI:DecidableEq L.UP:=L.inst10
  intro n p k sr D hn hp hk hs hp1 hk1 hs1 hbudgetR hbudgetI hC hP hbudgetLoad FR FS hdegR hdegS σ' H'
  have hstate:∀ e,L.σBase (Sum.inl e)≠σ' (Sum.inl e)→e∈FR.edgeFinset:=by
    intro e h
    by_contra he
    simp [σ',rawMarkedDeleteRims,he] at h
  have hRim:=marked_rim_change_of_raw_state_change L.PP L.πP d L.σBase σ' FR hstate
  have hSpoke:∀ b v u,¬(L.HBase b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u):=by
    intro b v u h
    by_contra he
    simp [H',markedDeletePhysicalSpokes,he] at h
  have hsub:∀ b v u,H' b v u→L.HBase b v u:=fun _ _ _ h=>h.1
  exact marked_reference_two_stage_inputs_after_changes L eps₁ eps₂ θ pstar ζ hreg hζ hpstar hB
    hn hp hk hs hp1 hk1 hs1 hbudgetR hbudgetI hC hP hbudgetLoad σ' H' FR FS hRim hSpoke hsub hdegR hdegS
end Oberwolfach
