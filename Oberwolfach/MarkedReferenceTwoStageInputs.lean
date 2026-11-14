module

public import Oberwolfach.MarkedReferenceLevelData
public import Oberwolfach.MarkedSpokeToleranceMonotone
public import Oberwolfach.MarkedLocalPrerequisiteMonotone

@[expose] public section
/-! The stored parent-level estimates imply the sampled two-stage inputs
when the displayed tolerances are ordered. The outcome and weight are fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}
theorem marked_reference_level_two_stage_sample_inputs
    (L:MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (eps₁ eps₂ θ:ℝ) (hreg:kappa≤eps₂) (herror:kappa/4≤min eps₁ eps₂)
    (hcounts:2*β≤3*(min betaA (t/4))) (hload:thetaDeep/4≤θ/2):
    letI:Fintype L.VP:=L.inst7
    letI:Fintype L.UP:=L.inst8
    letI:LinearOrder L.VP:=L.inst9
    letI:DecidableEq L.UP:=L.inst10
    let p:=rho*(r+4:ℝ)*t/2
    let k:=rho*t/2
    let sr:=(r+4:ℝ)*t
    let D:=2*Fintype.card L.UP/rho;
    (∀ v,|(L.PP.degree v:ℝ)-D|≤eps₂*Fintype.card L.VP) ∧
    (∀ u,L.qP u L.aP=t) ∧ (∀ u,L.sP u L.cP=sr) ∧
    MarkedRowsWithSpokes L.PP L.πP d (r+12) Finset.univ p k L.qP L.sP L.aP L.cP
      (min eps₁ eps₂*Fintype.card L.VP) L.σBase L.HBase ∧
    MarkedIndicesWithSpokes L.πP d (r+12) Finset.univ L.qP L.sP L.aP L.cP
      (min eps₁ eps₂*Fintype.card L.VP) L.σBase L.HBase ∧
    SuccessorSequenceWeightConditions L.PP L.πP (3*d) D L.tauRef aLoA BA L.weightRef ∧
    MarkedLocalConfigurationsWithSpokes r L.PP L.πP d Finset.univ (2*β) (2*β) L.σBase L.HBase ∧
    MarkedLocalSpokeLoadsWithSpokes L.PP L.πP d (r+4) D p k sr L.weightRef (θ/2) L.σBase L.HBase ∧
    (∀ v u,¬(L.HBase false v u∧L.HBase true v u)) ∧
    (∀ u v z,L.HBase false v u→L.HBase true z u→v≠L.πP z):=by
  letI:Fintype L.VP:=L.inst7
  letI:Fintype L.UP:=L.inst8
  letI:LinearOrder L.VP:=L.inst9
  letI:DecidableEq L.UP:=L.inst10
  intro p k sr D
  have hnonzero:(r+4:ℝ)≠0:=by positivity
  have hkr:rho*(r+4:ℝ)*t/2/(r+4:ℝ)=rho*t/2:=by field_simp
  have hn0:0≤(Fintype.card L.VP:ℝ):=Nat.cast_nonneg _
  have hrt:(kappa/4)*Fintype.card L.VP≤min eps₁ eps₂*Fintype.card L.VP:=
    mul_le_mul_of_nonneg_right herror hn0
  have hrows:=marked_rows_with_spokes_tolerance_mono L.PP L.πP d (r+12) Finset.univ p k L.qP L.sP L.aP L.cP _ _ L.σBase L.HBase hrt
    (by simpa only [p,k,hkr] using L.hrowsP0)
  have hindices:=marked_indices_with_spokes_tolerance_mono L.πP d (r+12) Finset.univ L.qP L.sP L.aP L.cP _ _ L.σBase L.HBase hrt L.hindicesP0
  have hconfigs:=marked_local_configurations_with_spokes_mono r L.PP L.πP d Finset.univ _ _ (2*β) (2*β) L.σBase L.HBase hcounts hcounts L.hDeepConfigs0
  have hloads:=marked_local_spoke_loads_tolerance_mono L.PP L.πP d (r+4) D p k sr L.weightRef _ _ L.σBase L.HBase hload
    (by simpa only [D,p,k,sr,hkr] using L.hDeepLoad0)
  refine ⟨fun v=>(L.hPreg v).trans (mul_le_mul_of_nonneg_right hreg hn0),L.hqP,L.hsP,hrows,hindices,L.hwRef,hconfigs,hloads,?_,L.hsepBase⟩
  exact fun v u=>L.hdtypesBase u v
end Oberwolfach
