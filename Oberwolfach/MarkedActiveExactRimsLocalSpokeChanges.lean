module

public import Oberwolfach.MarkedActiveFieldsRowsLocalChanges
public import Oberwolfach.MarkedRestrictedRimsExactOnProtected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_active_fields_rows_exact_rims_local_spoke_changes
    (r:ℕ) (α tstar kstar ζCfg η B pstar:ℝ)
    (hζCfg:0<ζCfg) (hη:0<η) (hB:0≤B) (hpstar:0<pstar) (htstar:0<tstar):
    ∃ ζcap:ℝ,0<ζcap ∧ ∀ ζ:ℝ,0≤ζ→ζ≤ζcap→
    ∀ (W Z Γ Color:Type) [Fintype W] [Fintype Z] [Fintype Γ] [Fintype Color]
      [LinearOrder W] [DecidableEq Z],
    ∀ (P:SimpleGraph W) (ρ:Equiv.Perm W) (d:ℕ)
      (D t τ A eps βrec p k s₀:ℝ) (weight:(Fin (r+4+1)→W)→ℝ)
      (q:Z→Γ→ℝ) (s:Z→Color→ℝ) (a:Γ) (j:Color)
      (σ σ':RawMarkedOutcome W Z Γ Color) (H H':Bool→W→Z→Prop)
      (FS:SimpleGraph (W⊕Z)),
    0<Fintype.card W →
    rawMarkedPairRims P ρ d σ=rawMarkedPairRims P ρ d σ'→
    (∀b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
    (∀z,(FS.degree z:ℝ)≤ζ*Fintype.card W)→
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
  obtain ⟨ζcap,hcap,htransfer⟩:=marked_active_fields_rows_local_changes r α tstar kstar ζCfg η B pstar hζCfg hη hB hpstar htstar
  refine ⟨ζcap,hcap,?_⟩
  intro ζ hζ hζcap W Z Γ Color _ _ _ _ _ _ P ρ d D t τ A eps βrec p k s₀ weight q s a j σ σ' H H' FS
    hn hrim hS hFS htypes hcycle hpath hβt htt heps hDlo hDhi hp hk hs hp1 hk1 hs1 hw hrow hcfg hload
  have hR:∀e,¬(rawMarkedPairRims P ρ d σ e↔rawMarkedPairRims P ρ d σ' e)→markedPairPhysical ρ e∈(⊥:SimpleGraph W).edgeFinset:=by
    intro e h
    exact False.elim (h (Iff.of_eq (congrFun hrim e)))
  have hFR:∀v,((⊥:SimpleGraph W).degree v:ℝ)≤ζ*Fintype.card W:=by
    intro v
    simp only [←SimpleGraph.card_neighborFinset_eq_degree]
    simpa using (mul_nonneg hζ (Nat.cast_nonneg (Fintype.card W)))
  exact htransfer ζ hζ hζcap W Z Γ Color P ρ d D t τ A eps βrec p k s₀ weight q s a j σ σ' H H' ⊥ FS
    hn (by intro e h; exact False.elim (h (Iff.of_eq (congrFun hrim e)))) hS (by intro v; convert hFR v using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _) hFS htypes hcycle hpath hβt htt heps hDlo hDhi hp hk hs hp1 hk1 hs1 hw hrow hcfg hload
end Oberwolfach
