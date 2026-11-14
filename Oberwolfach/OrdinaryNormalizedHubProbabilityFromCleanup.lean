module

public import Oberwolfach.OrdinaryNormalizedHubFactorsOnPhysicalSample
public import Oberwolfach.OrdinaryGeneralRelativeHubConditionsFromCleanup
public import Oberwolfach.OrdinaryNormalizedHubConflictDegree

@[expose] public section
/-! The sampled cleanup profile supplies the normalized hub geometry;
the fixed conflict-degree cost is absorbed by a sufficiently large inner set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_normalized_hub_probability_from_cleanup
    (m:ℕ) (hm:3≤m) (γ b B:ℝ) (hγ:0<γ) (hb:0<b) (hB:0≤B):
    ∃η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀(b₀ q:ℕ) (p:ℝ) (hp:0<p) (hp1:p≤1),∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
      (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
      (pR pH density tR tH L βe βh:ℝ) (σ:RawWheelOutcome V U Γ Color),
    OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH L βe βh s j σ→
    A.Nonempty→N≤A.card→Fintype.card {u:U // u∉Z}≤A.card^2→
    γ*A.card≤βe*Fintype.card (V⊕U)→(∀v,F.degree v≤b₀)→
    OrdinaryMixedHubWeightsInnerScale m b B η Q F H A Z→
    1-1/(A.card:ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (OrdinaryNormalizedHubFactorEvent m Q F H A Z p ζ):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hbase⟩:=ordinary_normalized_hub_factors_on_physical_sample m (by omega) γ b B hγ hb hB
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro b₀ q p hp hp1
  obtain ⟨Nf,hNf⟩:=hbase p hp hp1 q
  obtain ⟨M,hM⟩:=exists_nat_gt ((b₀:ℝ)/(ε*γ))
  refine ⟨max Nf M,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P Q F H A Z π d j s pR pH density tR tH L βe βh σ profile
    hA hn hJ hscale hF data
  have hpos:0<A.card:=Finset.card_pos.mpr hA
  have hM':(M:ℝ)≤A.card:=by exact_mod_cast (show M≤A.card by omega)
  have heγ:0<ε*γ:=mul_pos hε hγ
  have hsmall:(b₀:ℝ)≤ε*(γ*A.card):=by
    have hh:=mul_le_mul_of_nonneg_right (hM.le.trans hM') heγ.le
    have he:((b₀:ℝ)/(ε*γ))*(ε*γ)=b₀:=div_mul_cancel₀ _ heγ.ne'
    rw [he] at hh
    nlinarith only [hh]
  have hc:=ordinary_general_relative_hub_conditions_from_cleanup P Q F H A Z π d j s γ pR pH density tR tH L βe βh σ
    profile hA hscale
  have hFreal:∀v,(F.degree v:ℝ)≤b₀:=by intro v;exact_mod_cast hF v
  have hconf:=ordinary_normalized_hub_conflict_degree F H A Z γ ε b₀ hε.le hFreal hsmall hc.1
  exact hNf V U Q F H A Z (by omega) hpos hJ hc.1
    (by simpa only [show ¬m=2 by omega,ite_false] using hc.2) hconf data
end Oberwolfach
