module

public import Oberwolfach.MarkedDeepPerturbationSlack

@[expose] public section
/-! The parent local configurations and fixed-weight loads remain valid
after the same bounded physical changes, with a uniformly chosen allowance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_deep_fields_uniform_perturbation_below_cap
    (r:ℕ) (α tstar kstar ζCfg theta B pstar:ℝ)
    (hζCfg:0<ζCfg) (hθ:0<theta) (hB:0≤B) (hpstar:0<pstar):
    ∃ ζcap:ℝ,0<ζcap ∧ ∀ ζ:ℝ,0≤ζ→ζ≤ζcap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
      (rho t τ A eps βA:ℝ) (weight:(Fin (r+4+1)→V)→ℝ)
      (σ σ':RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    0<Fintype.card V →
    (∀ e,¬(rawMarkedPairRims P π d σ e↔rawMarkedPairRims P π d σ' e)→markedPairPhysical π e∈FR.edgeFinset) →
    (∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)) →
    (∀ v,(FR.degree v:ℝ)≤ζ*Fintype.card V) →
    (∀ z,(FS.degree z:ℝ)≤ζ*Fintype.card V) →
    (∀ v u,¬(H false v u∧H true v u)) →
    3*βA≤markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*ζCfg →
    3*βA≤markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*ζCfg →
    eps≤theta/8 →
    let DRef:=2*Fintype.card U/rho
    let pRef:=rho*(r+4:ℝ)*t/2
    let kRef:=pRef/(r+4:ℝ)
    let sRef:=(r+4:ℝ)*t;
    (Fintype.card V:ℝ)/2≤DRef → DRef≤2*Fintype.card V →
    pstar≤pRef → pstar≤kRef → pstar≤sRef → pRef≤1 → kRef≤1 → sRef≤1 →
    SuccessorSequenceWeightConditions P π (3*d) DRef τ A B weight →
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ
      (markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*(ζCfg/2))
      (markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*(ζCfg/2)) σ H →
    MarkedLocalSpokeLoadsWithSpokes P π d (r+4) DRef pRef kRef sRef weight eps σ H →
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ
      (3*min βA (t/4)) (3*min βA (t/4)) σ' H' ∧
    MarkedLocalSpokeLoadsWithSpokes P π d (r+4) DRef pRef kRef sRef weight (theta/4) σ' H' := by
  obtain ⟨ζcap,hζcap,hmargin⟩:=marked_deep_perturbation_slack r α tstar kstar ζCfg theta B pstar hζCfg hθ hB hpstar
  refine ⟨ζcap,hζcap,?_⟩
  intro ζ hζ hζle V U Γ Color _ _ _ _ _ _ P π d rho t τ A eps βA weight σ σ' H H' FR FS
    hn hR hS hFR hFS htypes hcycle hpath heps DRef pRef kRef sRef hDlo hDhi hp hk hs hp1 hk1 hs1 hw hcfg hload
  have hnR:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
  have hFRcap:∀ v,(FR.degree v:ℝ)≤ζcap*Fintype.card V := fun v=>(hFR v).trans (mul_le_mul_of_nonneg_right hζle hnR)
  have hFScap:∀ z,(FS.degree z:ℝ)≤ζcap*Fintype.card V := fun z=>(hFS z).trans (mul_le_mul_of_nonneg_right hζle hnR)
  obtain ⟨hC,hP,hbudget⟩:=hmargin βA t eps hcycle hpath heps
  exact marked_reference_deep_fields_after_changes r P π d hn rho t τ A B pstar eps ζcap theta
    _ _ βA hζcap.le hB hpstar weight σ σ' H H' FR FS hR hS hFRcap hFScap htypes hC hP
    hDlo hDhi hp hk hs hp1 hk1 hs1 hw hcfg hload hbudget
end Oberwolfach
