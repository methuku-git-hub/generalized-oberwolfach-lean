module

public import Oberwolfach.MarkedCommonFieldsUniformPerturbationBelowCap
public import Oberwolfach.MarkedDeepFieldsUniformPerturbationBelowCap
public import Oberwolfach.MarkedFiniteBalanceFamilySharedChanges

@[expose] public section
/-! Transfer the common fields, the deeper fields and all inner/deeper
balance tests on the same sample using one shared pair of change graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_common_deep_balance_shared_transfer
    (r:ℕ) (κ αC ω plo klo αD tstar kstar ζCfg theta B pstar etaBal x iota:ℝ)
    (hκ:0<κ) (hα:0<αC) (hω:0<ω) (hp:0<plo) (hk:0<klo)
    (hζCfg:0<ζCfg) (hθ:0<theta) (hB:0≤B) (hpstar:0<pstar)
    (hη:0<etaBal) (hx:0<x) (hi:0 < iota):
    ∃cap:ℝ,0<cap ∧ ∀ζ:ℝ,0≤ζ→ζ≤cap→
    ∀ (V U Γ Color I:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (g:Γ) (j:Color)
      (rho t βA τweight Aweight eps:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ)
      (weight:(Fin (r+4+1)→V)→ℝ)
      (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)) (Av:I→Finset V) (Bu:I→Finset U) (err0:I→ℝ),
    0<Fintype.card V→ω*Fintype.card V≤(Fintype.card U:ℝ)→
    (∀e,σ (Sum.inr e)=τ (Sum.inr e))→
    (∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset)→
    (∀b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
    (∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V)→(∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V)→
    (∀v u,¬(H false v u∧H true v u))→(∀v u,¬(H' false v u∧H' true v u))→
    3*βA≤markedLocalCycleCoefficient r αD (tstar/2) kstar-(r+5:ℕ)*ζCfg→
    3*βA≤markedLocalPathCoefficient r αD (tstar/2) kstar-(r+4:ℕ)*ζCfg→eps≤theta/8→
    (∀i,0≤err0 i)→(∀i,iota*Fintype.card V≤((Av i).card:ℝ))→
    (∀i,err0 i≤(etaBal/2)*(Av i).card)→(∀i,err0 i≤(x/4)*Fintype.card V)→
    let DRef:=2*Fintype.card U/rho
    let p:=rho*(r+4:ℝ)*t/2
    let k:=p/(r+4:ℝ)
    let sr:=(r+4:ℝ)*t
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    let E':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true
    let S':=Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)
    let err:=fun i=>err0 i+((r+4)+4:ℕ)*ζ*Fintype.card V;
    plo≤p→klo≤k→(Fintype.card V:ℝ)/2≤DRef→DRef≤2*Fintype.card V→
    pstar≤p→pstar≤k→pstar≤sr→p≤1→k≤1→sr≤1→
    SuccessorSequenceWeightConditions P π (3*d) DRef τweight Aweight B weight→
    MarkedReferenceStatistics P π d g j DRef (κ/8) (κ/2) (αC/8) p k sr t σ→
    MarkedReferenceCutFamilies P π d g j (αC/8) p k t σ→
    MarkedRowsWithSpokes P π d (r+12) Finset.univ p k q s g j ((κ/8)*Fintype.card V) σ H→
    MarkedIndicesWithSpokes π d (r+12) Finset.univ q s g j ((κ/8)*Fintype.card V) σ H→
    MarkedCommonConfigurationsWithSpokes r P π d βA (κ/8) σ H→
    (∀b v,(∑u,if ¬(rawMarkedPairSpokes π d σ g j b v u↔H b v u) then (1:ℝ) else 0)≤(κ/8)*Fintype.card U)→
    (∀b u,(∑v,if ¬(rawMarkedPairSpokes π d σ g j b v u↔H b v u) then (1:ℝ) else 0)≤(κ/8)*Fintype.card V)→
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ
      (markedLocalCycleCoefficient r αD (tstar/2) kstar-(r+5:ℕ)*(ζCfg/2))
      (markedLocalPathCoefficient r αD (tstar/2) kstar-(r+4:ℕ)*(ζCfg/2)) σ H→
    MarkedLocalSpokeLoadsWithSpokes P π d (r+4) DRef p k sr weight eps σ H→
    (∀i z a,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S (r+4) (Av i) (Bu i) z a|≤err0 i)→
    (MarkedReferenceStatistics P π d g j DRef (κ/4) κ (αC/16) p k sr t τ ∧
     MarkedReferenceCutFamilies P π d g j (αC/16) p k t τ ∧
     MarkedCommonConfigurationsWithSpokes r P π d βA (κ/4) τ H' ∧
     MarkedRowsWithSpokes P π d (r+12) Finset.univ p k q s g j ((κ/4)*Fintype.card V) τ H' ∧
     MarkedIndicesWithSpokes π d (r+12) Finset.univ q s g j ((κ/4)*Fintype.card V) τ H' ∧
     (∀b v,(∑u,if ¬(rawMarkedPairSpokes π d τ g j b v u↔H' b v u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card U) ∧
     (∀b u,(∑v,if ¬(rawMarkedPairSpokes π d τ g j b v u↔H' b v u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card V)) ∧
    (MarkedLocalConfigurationsWithSpokes r P π d Finset.univ (3*min βA (t/4)) (3*min βA (t/4)) τ H' ∧
     MarkedLocalSpokeLoadsWithSpokes P π d (r+4) DRef p k sr weight (theta/4) τ H') ∧
    (∀i,0≤err i ∧ err i≤etaBal*(Av i).card ∧ err i≤(x/2)*Fintype.card V ∧
      ∀z a,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' (r+4) (Av i) (Bu i) z a|≤err i):=by
  obtain ⟨c,hc,hcommon⟩:=marked_common_fields_uniform_perturbation_below_cap r κ αC ω plo klo hκ hα hω hp hk
  obtain ⟨d,hd,hdeep⟩:=marked_deep_fields_uniform_perturbation_below_cap r αD tstar kstar ζCfg theta B pstar hζCfg hθ hB hpstar
  obtain ⟨b,hb,hbalance⟩:=marked_finite_balance_family_shared_changes (r+4) etaBal x iota hη hx hi
  refine ⟨min c (min d b),lt_min hc (lt_min hd hb),?_⟩
  intro ζ hζ hζcap V U Γ Color I _ _ _ _ _ _ P π dim g j rho t βA τweight Aweight eps q s weight σ τ H H' FR FS Av Bu err0 hn hU hinterval hR hS hFR hFS hH hH' hcycle hpath heps herr0 hsize herrA herrN DRef p k sr E K S E' K' S' err hp' hk' hDlo hDhi hp0 hk0 hs0 hp1 hk1 hs1 hw hstats hcuts hrows hindices hcfg hOldRow hOldCol hdeepcfg hload hfinite
  have hζc:ζ≤c:=hζcap.trans (min_le_left _ _)
  have hζd:ζ≤d:=hζcap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hζb:ζ≤b:=hζcap.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨?_,?_,?_⟩
  · exact hcommon ζ hζ hζc V U Γ Color P π dim g j rho t DRef βA q s σ τ H H' FR FS
      hn hU hinterval hR hS hFR hFS hH hp' hk' hstats hcuts hrows hindices hcfg hOldRow hOldCol
  · exact hdeep ζ hζ hζd V U Γ Color P π dim rho t τweight Aweight eps βA weight σ τ H H' FR FS
      hn hR hS hFR hFS hH hcycle hpath heps hDlo hDhi hp0 hk0 hs0 hp1 hk1 hs1 hw hdeepcfg hload
  · exact hbalance ζ hζ hζb V U Γ Color I P π dim σ τ H H' FR FS Av Bu err0
      herr0 hsize herrA herrN hH hH' hR hS hFR hFS hfinite
end Oberwolfach
