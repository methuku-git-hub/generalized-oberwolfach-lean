module

public import Oberwolfach.MarkedReferenceTwoStageDeletionInputs
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
theorem marked_reference_two_stage_uniform_deletion_inputs
    (betaCap:ℝ) (hbetaA:0<betaA) (ht:0<t) (hbetaCap:0<betaCap):
    ∃ beta:ℝ,0<beta∧beta≤t/2∧beta≤betaCap∧
    ∀ eps₁ eps₂ θ pstar cap:ℝ,0<eps₁→0<eps₂→0<θ→0<pstar→0<cap→0≤BA→
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
    pstar≤p→pstar≤k→pstar≤sr→p≤1→k≤1→sr≤1→
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
  obtain ⟨beta,hbeta,hbetat,hbetacap,hchoose⟩:=
    marked_reference_choose_uniform_change_margins r betaA t betaCap hbetaA ht hbetaCap
  refine ⟨beta,hbeta,hbetat,hbetacap,?_⟩
  intro eps₁ eps₂ θ pstar cap he₁ he₂ hθ hpstar hcap hB
  let coeff:ℝ:=15*((r+4:ℝ)+1)^4*(2*BA/pstar^(2*(r+4)+1))
  have hc:0≤coeff:=marked_reference_weighted_change_coefficient_nonnegative r BA pstar hB hpstar
  obtain ⟨kappa,thetaDeep,ζ,hκ,hθD,hζ,hκcap,hθcap,hζcap,hreg,hR,hI,hC,hP,hload⟩:=
    hchoose eps₁ eps₂ θ coeff cap he₁ he₂ hθ hc hcap
  refine ⟨kappa,thetaDeep,ζ,hκ,hθD,hζ,hκcap,hθcap,hζcap,?_⟩
  intro L
  letI:Fintype L.VP:=L.inst7
  letI:Fintype L.UP:=L.inst8
  letI:LinearOrder L.VP:=L.inst9
  letI:DecidableEq L.UP:=L.inst10
  intro n p k sr D hn hp hk hs hp1 hk1 hs1 FR FS hdegR hdegS σ' H'
  have hscaled:=marked_reference_scale_neighbourhood_margins r kappa ζ eps₁ eps₂ n (Nat.cast_nonneg _) hR hI
  exact marked_reference_two_stage_inputs_after_deletions L eps₁ eps₂ θ pstar ζ hreg hζ.le hpstar hB
    hn hp hk hs hp1 hk1 hs1 hscaled.1 hscaled.2 hC hP hload FR FS hdegR hdegS
end Oberwolfach
