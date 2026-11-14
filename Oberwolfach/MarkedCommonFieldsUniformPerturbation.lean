module

public import Oberwolfach.MarkedReferenceCommonFieldsAfterChanges
public import Oberwolfach.MarkedReferencePerturbationSlack
public import Oberwolfach.MarkedReferenceStatisticsDeltaMonotone

@[expose] public section
/-! Common reference fields survive a fixed small physical perturbation,
with the allowance chosen uniformly from density lower bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_common_fields_uniform_perturbation
    (r:ℕ) (κ α ω plo klo:ℝ)
    (hκ:0<κ) (hα:0<α) (hω:0<ω) (hp:0<plo) (hk:0<klo):
    ∃ ζ:ℝ,0<ζ ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (g:Γ) (j:Color)
      (rho t D βA:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ)
      (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    0<Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) →
    (∀ e,σ (Sum.inr e)=τ (Sum.inr e)) →
    (∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset) →
    (∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)) →
    (∀ v,(FR.degree v:ℝ)≤ζ*Fintype.card V) →
    (∀ z,(FS.degree z:ℝ)≤ζ*Fintype.card V) →
    (∀ v u,¬(H false v u∧H true v u)) →
    let p:=rho*(r+4:ℝ)*t/2
    let k:=p/(r+4:ℝ);
    plo≤p → klo≤k →
    MarkedReferenceStatistics P π d g j D (κ/8) (κ/2) (α/8) p k ((r+4:ℝ)*t) t σ →
    MarkedReferenceCutFamilies P π d g j (α/8) p k t σ →
    MarkedRowsWithSpokes P π d (r+12) Finset.univ p k q s g j ((κ/8)*Fintype.card V) σ H →
    MarkedIndicesWithSpokes π d (r+12) Finset.univ q s g j ((κ/8)*Fintype.card V) σ H →
    MarkedCommonConfigurationsWithSpokes r P π d βA (κ/8) σ H →
    (∀ b v,(∑ u,if ¬(rawMarkedPairSpokes π d σ g j b v u↔H b v u) then (1:ℝ) else 0)≤(κ/8)*Fintype.card U) →
    (∀ b u,(∑ v,if ¬(rawMarkedPairSpokes π d σ g j b v u↔H b v u) then (1:ℝ) else 0)≤(κ/8)*Fintype.card V) →
    MarkedReferenceStatistics P π d g j D (κ/4) κ (α/16) p k ((r+4:ℝ)*t) t τ ∧
    MarkedReferenceCutFamilies P π d g j (α/16) p k t τ ∧
    MarkedCommonConfigurationsWithSpokes r P π d βA (κ/4) τ H' ∧
    MarkedRowsWithSpokes P π d (r+12) Finset.univ p k q s g j ((κ/4)*Fintype.card V) τ H' ∧
    MarkedIndicesWithSpokes π d (r+12) Finset.univ q s g j ((κ/4)*Fintype.card V) τ H' ∧
    (∀ b v,(∑ u,if ¬(rawMarkedPairSpokes π d τ g j b v u↔H' b v u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card U) ∧
    (∀ b u,(∑ v,if ¬(rawMarkedPairSpokes π d τ g j b v u↔H' b v u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card V) := by
  obtain ⟨ζ,hζ,h₁,h₂,h₃,h₄,hωζ,hmargin,hrow⟩:=
    marked_reference_perturbation_slack (r+12) κ α ω plo klo hκ hα hω hp hk
  refine ⟨ζ,hζ,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P π d g j rho t D βA q s σ τ H H' FR FS hn hU hinterval hR hS hFR hFS htypes p k hp' hk' hstats hcuts hrows hindices hconfig hOldR hOldC
  have hnR:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
  have hbudgetR:(κ/8)*Fintype.card V+(r+12:ℝ)*(ζ*Fintype.card V+ζ*Fintype.card V)≤(κ/4)*Fintype.card V := by
    have hh:=mul_le_mul_of_nonneg_right h₂ hnR
    push_cast at hh
    nlinarith [hh]
  have hbudgetI:(κ/8)*Fintype.card V+(r+12:ℝ)*(ζ*Fintype.card V)≤(κ/4)*Fintype.card V := by
    have hh:=mul_le_mul_of_nonneg_right h₃ hnR
    push_cast at hh
    nlinarith [hh]
  have hOldRow:(κ/8)*Fintype.card U+ζ*Fintype.card V≤(κ/4)*Fintype.card U :=
    hrow _ _ hnR hU
  have hOldCol:(κ/8)*Fintype.card V+ζ*Fintype.card V≤(κ/4)*Fintype.card V := by
    nlinarith [mul_le_mul_of_nonneg_right h₁ hnR]
  have hcut:∀ mark:Bool,ζ≤(α/8-2*(α/32))*(if mark then k else p)/4 := by
    intro b
    have hm:ζ≤(α/8-α/16)*min p k/4 := (hmargin p k hp' hk').2
    have hmk:min p k≤(if b then k else p):=by cases b <;> simp [min_le_left,min_le_right]
    have hh:=mul_le_mul_of_nonneg_left hmk (show 0≤(α/8-α/16)/4 by linarith)
    nlinarith
  have hstep:2*ζ≤(3/2)*(α/8-2*(α/32))*p^2 := by
    have hh:=(hmargin p k hp' hk').1
    nlinarith
  have hstats' : MarkedReferenceStatistics P π d g j D (κ/8) κ (α/8) p k ((r+4:ℝ)*t) t σ :=
    marked_reference_statistics_delta_mono P π d g j D (κ/8) (κ/2) κ (α/8) p k ((r+4:ℝ)*t) t σ (by linarith) hstats
  have hmain:=marked_reference_common_fields_after_changes P π d r g j rho t (α/32) κ D (κ/8) (α/8) (α/8) βA (κ/8) ζ
    ((κ/8)*Fintype.card V) ((κ/8)*Fintype.card V) ((κ/8)*Fintype.card U) ((κ/8)*Fintype.card V)
    hζ.le hn q s σ τ H H' FR FS hinterval hR hS hFR hFS htypes h₁ (by linarith) hstep hcut hbudgetR hbudgetI h₄ hOldRow hOldCol
    hstats' hcuts hrows hindices hconfig hOldR hOldC
  simpa only [show 2*(α/32)=α/16 by ring] using hmain
end Oberwolfach
