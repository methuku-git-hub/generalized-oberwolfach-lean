module

public import Oberwolfach.MarkedReferenceTwoStageUniformDeletion
public import Oberwolfach.MarkedTwoStageCompleteDensityBounds
public import Oberwolfach.MarkedReferenceAdaptiveScaledMargins

@[expose] public section
/-! Select the configuration parameter before the two-stage constants and
then choose arbitrarily small uniform deletion margins afterwards. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA ξ alphaInner omegaInner
  iota aLo B η x omegaI hIcut deltaI etaBal:ℝ}
theorem marked_reference_two_stage_uniform_canonical_deletion_inputs
    (betaCap:ℝ) (hbetaA:0<betaA) (ht:0<t) (hbetaCap:0<betaCap)
    (hrho:0<rho) (hrho1:rho≤1) (hst:(((r+1)+3:ℕ):ℝ)*t≤1):
    ∃ beta:ℝ,0<beta∧beta≤t/2∧beta≤betaCap∧
    ∀ eps₁ eps₂ θ cap:ℝ,0<eps₁→0<eps₂→0<θ→0<cap→0≤BA→
    ∃ kappa thetaDeep ζ:ℝ,0<kappa∧0<thetaDeep∧0<ζ∧kappa≤cap∧thetaDeep≤cap∧ζ≤cap∧
    ∀ (L:MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota beta aLo B η x omegaI hIcut deltaI etaBal),
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
    MarkedLocalConfigurationsWithSpokes r L.PP L.πP d Finset.univ (2*beta) (2*beta) σ' H' ∧
    MarkedLocalSpokeLoadsWithSpokes L.PP L.πP d (r+4) D p k sr L.weightRef (θ/2) σ' H' ∧
    (∀ v u,¬(H' false v u∧H' true v u)) ∧
    (∀ u v z,H' false v u→H' true z u→v≠L.πP z)  :=by
  obtain ⟨beta,hbeta,hbetat,hbetacap,hbase⟩:=
    marked_reference_two_stage_uniform_deletion_inputs (Gamma:=Gamma) (Color:=Color) (r:=r) (d:=d) (N:=N) (NI:=NI) (Kgeom:=Kgeom)
      (gamma:=gamma) (rho:=rho) (omega:=omega) (t:=t) (p0:=p0) (betaA:=betaA) (aLoA:=aLoA) (BA:=BA)
      (ξ:=ξ) (alphaInner:=alphaInner) (omegaInner:=omegaInner) (iota:=iota) (aLo:=aLo) (B:=B) (η:=η)
      (x:=x) (omegaI:=omegaI) (hIcut:=hIcut) (deltaI:=deltaI) (etaBal:=etaBal) betaCap hbetaA ht hbetaCap
  refine ⟨beta,hbeta,hbetat,hbetacap,?_⟩
  intro eps₁ eps₂ θ cap he₁ he₂ hθ hcap hB
  have hb:=marked_two_stage_complete_density_bounds r t rho ht hrho hrho1 hst
  obtain ⟨kappa,thetaDeep,ζ,hκ,hθD,hζ,hκcap,hθcap,hζcap,hresult⟩:=
    hbase eps₁ eps₂ θ (rho*t/2) cap he₁ he₂ hθ hb.1 hcap hB
  refine ⟨kappa,thetaDeep,ζ,hκ,hθD,hζ,hκcap,hθcap,hζcap,?_⟩
  intro L
  letI:Fintype L.VP:=L.inst7
  letI:Fintype L.UP:=L.inst8
  letI:LinearOrder L.VP:=L.inst9
  letI:DecidableEq L.UP:=L.inst10
  intro n p k sr D hn FR FS hdegR hdegS σ' H'
  have hp:rho*t/2≤p:=by dsimp only [p];push_cast;have h:=hb.2.1;push_cast at h;nlinarith [h]
  have hk:rho*t/2≤k:=le_refl _
  have hs:rho*t/2≤sr:=by dsimp only [sr];push_cast;have h:=hb.2.2.2.1;push_cast at h;nlinarith [h]
  have hp1:p≤1:=by dsimp only [p];push_cast;have h:=hb.2.2.2.2.1;push_cast at h;nlinarith [h]
  have hk1:k≤1:=hb.2.2.2.2.2.1
  have hs1:sr≤1:=by dsimp only [sr];push_cast;have h:=hb.2.2.2.2.2.2;push_cast at h;nlinarith [h]
  exact hresult L hn hp hk hs hp1 hk1 hs1 FR FS hdegR hdegS
end Oberwolfach
