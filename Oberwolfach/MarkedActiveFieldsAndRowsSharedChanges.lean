module

public import Oberwolfach.MarkedActiveFieldsUniformPhysicalChanges
public import Oberwolfach.MarkedActiveRowsUniformPhysicalChanges
public import Oberwolfach.MarkedDeepPerturbationSlack
public import Oberwolfach.MarkedLocalChangeDegreeScale
public import Oberwolfach.MarkedPhysicalChangesRestrict
public import Oberwolfach.MarkedReferenceDeepConfigurationsAfterChanges
public import Oberwolfach.MarkedLocalSpokeLoadSharedChanges

@[expose] public section
/-! On the active vertex domain and the original non-deeper hub domain,
transfer local configurations and fixed-weight loads using one global
physical-change allowance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_active_fields_and_rows_shared_physical_changes
    (r:ℕ) (α tstar kstar ζCfg η B pstar iota:ℝ)
    (hζCfg:0<ζCfg) (hη:0<η) (hB:0≤B) (hpstar:0<pstar) (hi:0 < iota) (htstar:0<tstar):
    ∃ ζcap:ℝ,0<ζcap ∧ ∀ ζ:ℝ,0≤ζ→ζ≤ζcap→
    ∀ (V U W Z Γ Color:Type) [Fintype V] [Fintype U] [Fintype W] [Fintype Z]
      [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z],
    ∀ (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
      (hcomm:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d:ℕ)
      (D t τ A eps βrec p k s₀:ℝ) (weight:(Fin (r+4+1)→W)→ℝ)
      (q:Z→Γ→ℝ) (s:Z→Color→ℝ) (a:Γ) (j:Color)
      (σ σ':RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    0<Fintype.card W → iota*Fintype.card V≤(Fintype.card W:ℝ) →
    (∀ e,¬(rawMarkedPairRims P π d σ e↔rawMarkedPairRims P π d σ' e)→markedPairPhysical π e∈FR.edgeFinset) →
    (∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)) →
    (∀ v,(FR.degree v:ℝ)≤ζ*Fintype.card V) →
    (∀ z,(FS.degree z:ℝ)≤ζ*Fintype.card V) →
    (∀ v u,¬(H false v u∧H true v u)) →
    3*βrec≤markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*ζCfg →
    3*βrec≤markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*ζCfg →
    βrec≤t/4 → tstar≤t → eps≤η/8 →
    (Fintype.card W:ℝ)/2≤D → D≤2*Fintype.card W →
    pstar≤p → pstar≤k → pstar≤s₀ → p≤1 → k≤1 → s₀≤1 →
    SuccessorSequenceWeightConditions (P.comap f) ρ (3*d) D τ A B weight →
    let σloc:=rawMarkedRestrictPair f g σ
    let τloc:=rawMarkedRestrictPair f g σ'
    let Hloc:=fun b v u=>H b (f v) (g u)
    let Hloc':=fun b v u=>H' b (f v) (g u);
    MarkedRowsWithSpokes (P.comap f) ρ d 1 Finset.univ p k q s a j ((tstar/16)*Fintype.card W) σloc Hloc →
    MarkedLocalConfigurationsWithSpokes r (P.comap f) ρ d Finset.univ
      (markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*(ζCfg/2))
      (markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*(ζCfg/2)) σloc Hloc →
    MarkedLocalSpokeLoadsWithSpokes (P.comap f) ρ d (r+4) D p k s₀ weight eps σloc Hloc →
    MarkedLocalConfigurationsWithSpokes r (P.comap f) ρ d Finset.univ (3*βrec) (3*βrec) τloc Hloc' ∧
    MarkedLocalSpokeLoadsWithSpokes (P.comap f) ρ d (r+4) D p k s₀ weight (η/4) τloc Hloc' ∧
    MarkedRowsWithSpokes (P.comap f) ρ d 1 Finset.univ p k q s a j ((t/8)*Fintype.card W) τloc Hloc' := by
  obtain ⟨c,hc,hfields⟩:=marked_active_fields_uniform_physical_changes r α tstar kstar ζCfg η B pstar iota hζCfg hη hB hpstar hi
  obtain ⟨crows,hcrows,hrows⟩:=marked_active_rows_uniform_physical_changes tstar iota htstar hi
  refine ⟨min c crows,lt_min hc hcrows,?_⟩
  intro ζ hζ hζcap V U W Z Γ Color _ _ _ _ _ _ _ _ _ _ f g π ρ hcomm P d D t τ A eps βrec p k s₀ weight q s a j σ σ' H H' FR FS
    hn hsize hR hS hFR hFS htypes hcycle hpath hβt htt heps hDlo hDhi hp hk hs hp1 hk1 hs1 hw σloc τloc Hloc Hloc' hrow hcfg hload
  have hf:=hfields ζ hζ (hζcap.trans (min_le_left _ _)) V U W Z Γ Color f g π ρ hcomm P d D t τ A eps βrec p k s₀ weight σ σ' H H' FR FS
    hn hsize hR hS hFR hFS htypes hcycle hpath hβt heps hDlo hDhi hp hk hs hp1 hk1 hs1 hw hcfg hload
  have hr:=hrows ζ hζ (hζcap.trans (min_le_right _ _)) V U W Z Γ Color f g π ρ hcomm P d t p k q s a j σ σ' H H' FR FS
    hsize htt hR hS hFR hFS hrow
  exact ⟨hf.1,hf.2,hr⟩
end Oberwolfach
