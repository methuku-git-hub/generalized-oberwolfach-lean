module

public import Oberwolfach.OrdinaryNormalizedHubFactorsOnPhysicalSample
public import Oberwolfach.OrdinaryRelativeHubConditionsFromDeepSample
public import Oberwolfach.OrdinaryNormalizedHubConflictDegree

@[expose] public section
/-! The triangle hub factors can be normalized to the actual inner domain.
Their constants depend on the original sampling lower bound, not on the
vortex's inner-to-ambient size ratio. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_normalized_hub_probability_from_cleanup
    (pmin b B:ℝ) (hpmin:0<pmin) (hpmin1:pmin≤1) (hb:0<b) (hB:0≤B):
    ∃εbudget η ζ:ℝ,0<εbudget ∧ 0<η ∧ 0<ζ ∧
    ∀(b₀ q:ℕ) (p:ℝ) (hp:0<p) (hp1:p≤1),∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
      (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
      (pR pH density tR tH L Ledit βe βh:ℝ) (σ:RawWheelOutcome V U Γ Color),
    OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ→
    RawOrdinaryRows P π d 3 A pR s j tR σ→
    A.Nonempty→N≤A.card→Fintype.card {u:U // u∉Z}≤A.card^2→
    pmin≤pR→pmin≤pH→(3/4:ℝ)≤density→0≤L→0≤Ledit→L≤(A.card:ℝ)/24→
    (∀v,F.degree v≤b₀)→(∀v,(F.degree v:ℝ)≤L)→tR+4*Ledit≤εbudget*A.card→
    OrdinaryMixedHubWeightsInnerScale 2 b B η Q F H A Z→
    1-1/(A.card:ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (OrdinaryNormalizedHubFactorEvent 2 Q F H A Z p ζ):=by
  let γ:ℝ:=pmin^4/32
  have hγ:0<γ:=by dsimp [γ];positivity
  obtain ⟨εfactor,η,ζ,hεfactor,hη,hζ,hbase⟩:=
    ordinary_normalized_hub_factors_on_physical_sample 2 (by omega) γ b B hγ hb hB
  refine ⟨γ,η,ζ,hγ,hη,hζ,?_⟩
  intro b₀ q p hp hp1
  obtain ⟨Nf,hNf⟩:=hbase p hp hp1 q
  obtain ⟨M,hM⟩:=exists_nat_gt ((b₀:ℝ)/(εfactor*γ))
  refine ⟨max Nf M,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P Q F H A Z π d j s pR pH density tR tH L Ledit βe βh σ profile deep
    hA hn hJ hpR hpH hdensity hL hLedit hLA hF hFL hbudget data
  have hpos:0<A.card:=Finset.card_pos.mpr hA
  have hM':(M:ℝ)≤A.card:=by exact_mod_cast (show M≤A.card by omega)
  have heγ:0<εfactor*γ:=mul_pos hεfactor hγ
  have hsmall:(b₀:ℝ)≤εfactor*(γ*A.card):=by
    have hh:=mul_le_mul_of_nonneg_right (hM.le.trans hM') heγ.le
    have he:((b₀:ℝ)/(εfactor*γ))*(εfactor*γ)=b₀:=div_mul_cancel₀ _ heγ.ne'
    rw [he] at hh
    nlinarith only [hh]
  have hγcap:γ≤pmin^4/16:=by dsimp [γ];nlinarith [sq_nonneg (pmin^2)]
  have hc:=ordinary_relative_hub_conditions_from_deep_sample P Q F H A Z π d j s γ pmin pR pH density
    tR tH L Ledit βe βh γ σ profile deep hA hpmin hpmin1 hpR hpH hdensity hL hLedit hLA
    hFL hbudget hγcap hγcap
  have hFreal:∀v,(F.degree v:ℝ)≤b₀:=by intro v;exact_mod_cast hF v
  have hconf:=ordinary_normalized_hub_conflict_degree F H A Z γ εfactor b₀ hεfactor.le hFreal hsmall hc.1
  exact hNf V U Q F H A Z (by omega) hpos hJ hc.1
    (by simpa only [ite_true] using hc.2) hconf data
end Oberwolfach
