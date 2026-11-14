module

public import Oberwolfach.MarkedDeepPerturbationSlack
public import Oberwolfach.MarkedReferenceDeepConfigurationsAfterChanges
public import Oberwolfach.MarkedLocalSpokeLoadSharedChanges
public import Oberwolfach.MarkedRowsPhysicalChange

@[expose] public section
/-! Transfer first-active fields using changes measured on the active domain.
The tolerance is independent of the ratio between that domain and the host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_active_fields_rows_local_changes
    (r:ℕ) (α tstar kstar ζCfg η B pstar:ℝ)
    (hζCfg:0<ζCfg) (hη:0<η) (hB:0≤B) (hpstar:0<pstar) (htstar:0<tstar):
    ∃ ζcap:ℝ,0<ζcap ∧ ∀ ζ:ℝ,0≤ζ→ζ≤ζcap→
    ∀ (W Z Γ Color:Type) [Fintype W] [Fintype Z] [Fintype Γ] [Fintype Color]
      [LinearOrder W] [DecidableEq Z],
    ∀ (P:SimpleGraph W) (ρ:Equiv.Perm W) (d:ℕ)
      (D t τ A eps βrec p k s₀:ℝ) (weight:(Fin (r+4+1)→W)→ℝ)
      (q:Z→Γ→ℝ) (s:Z→Color→ℝ) (a:Γ) (j:Color)
      (σ σ':RawMarkedOutcome W Z Γ Color) (H H':Bool→W→Z→Prop)
      (FR:SimpleGraph W) (FS:SimpleGraph (W⊕Z)),
    0<Fintype.card W →
    (∀e,¬(rawMarkedPairRims P ρ d σ e↔rawMarkedPairRims P ρ d σ' e)→markedPairPhysical ρ e∈FR.edgeFinset)→
    (∀b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
    (∀v,(FR.degree v:ℝ)≤ζ*Fintype.card W)→(∀z,(FS.degree z:ℝ)≤ζ*Fintype.card W)→
    (∀v u,¬(H false v u∧H true v u))→
    3*βrec≤markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*ζCfg→
    3*βrec≤markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*ζCfg→
    βrec≤t/4→tstar≤t→eps≤η/8→
    (Fintype.card W:ℝ)/2≤D→D≤2*Fintype.card W→
    pstar≤p→pstar≤k→pstar≤s₀→p≤1→k≤1→s₀≤1→
    SuccessorSequenceWeightConditions P ρ (3*d) D τ A B weight→
    MarkedRowsWithSpokes P ρ d 1 Finset.univ p k q s a j ((tstar/16)*Fintype.card W) σ H→
    MarkedLocalConfigurationsWithSpokes r P ρ d Finset.univ
      (markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*(ζCfg/2))
      (markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*(ζCfg/2)) σ H→
    MarkedLocalSpokeLoadsWithSpokes P ρ d (r+4) D p k s₀ weight eps σ H→
    MarkedLocalConfigurationsWithSpokes r P ρ d Finset.univ (3*βrec) (3*βrec) σ' H' ∧
    MarkedLocalSpokeLoadsWithSpokes P ρ d (r+4) D p k s₀ weight (η/4) σ' H' ∧
    MarkedRowsWithSpokes P ρ d 1 Finset.univ p k q s a j ((t/8)*Fintype.card W) σ' H' :=by
  obtain ⟨ζlocal,hζlocal,hbudget⟩:=marked_deep_perturbation_slack r α tstar kstar ζCfg η B pstar hζCfg hη hB hpstar
  let ζrow:=tstar/32
  refine ⟨min ζlocal ζrow,lt_min hζlocal (by dsimp [ζrow];positivity),?_⟩
  intro ζ hζ hζcap W Z Γ Color _ _ _ _ _ _ P ρ d D t τ A eps βrec p k s₀ weight q s a j σ σ' H H' FR FS
    hn hR hS hFR hFS htypes hcycle hpath hβt htt heps hDlo hDhi hp hk hs hp1 hk1 hs1 hw hrow hcfg hload
  have hn0:(0:ℝ)≤Fintype.card W:=Nat.cast_nonneg _
  have hFRlocal:∀v,(FR.degree v:ℝ)≤ζlocal*Fintype.card W:=by
    intro v
    exact (hFR v).trans (mul_le_mul_of_nonneg_right (hζcap.trans (min_le_left _ _)) hn0)
  have hFSlocal:∀z,(FS.degree z:ℝ)≤ζlocal*Fintype.card W:=by
    intro z
    exact (hFS z).trans (mul_le_mul_of_nonneg_right (hζcap.trans (min_le_left _ _)) hn0)
  obtain ⟨hC,hP,hloadBudget⟩:=hbudget βrec t eps hcycle hpath heps
  have hconf:=marked_reference_deep_configurations_after_changes r P ρ d _ _ βrec t ζlocal
    σ σ' H H' FR FS hR hS hFRlocal hFSlocal htypes hC hP hcfg
  rw [min_eq_left hβt] at hconf
  have hload':=marked_local_spoke_loads_from_shared_changes P ρ d (r+4) (by omega) hn
    D τ A B hDlo hDhi p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB weight hw eps ζlocal (η/4) hζlocal.le
    σ σ' H H' hload FR FS hR hS hFRlocal hFSlocal (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hloadBudget)
  have hFRrow:∀v,(FR.degree v:ℝ)≤ζrow*Fintype.card W:=by
    intro v
    exact (hFR v).trans (mul_le_mul_of_nonneg_right (hζcap.trans (min_le_right _ _)) hn0)
  have hFSrow:∀z,(FS.degree z:ℝ)≤ζrow*Fintype.card W:=by
    intro z
    exact (hFS z).trans (mul_le_mul_of_nonneg_right (hζcap.trans (min_le_right _ _)) hn0)
  have hrowpos:0≤ζrow*Fintype.card W:=by dsimp [ζrow];positivity
  have hr:=marked_rows_after_physical_change P ρ d 1 Finset.univ p k q s a j
    ((tstar/16)*Fintype.card W) (ζrow*Fintype.card W) (ζrow*Fintype.card W) hrowpos hrowpos
    σ σ' H H' hrow FR FS hR hS hFRrow (fun u=>hFSrow (Sum.inr u))
  have hrowBudget:(tstar/16)*Fintype.card W+1*(ζrow*Fintype.card W+ζrow*Fintype.card W)≤
      (t/8)*Fintype.card W:=by dsimp [ζrow];nlinarith [mul_le_mul_of_nonneg_right htt hn0]
  refine ⟨hconf,hload',?_⟩
  intro S T J hS hT hJ hinj
  exact (hr S T J hS hT hJ hinj).trans_le (by simpa only [Nat.cast_one] using hrowBudget)
end Oberwolfach
