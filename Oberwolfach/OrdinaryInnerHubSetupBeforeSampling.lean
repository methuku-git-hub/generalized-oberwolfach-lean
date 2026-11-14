module

public import Oberwolfach.OrdinaryInnerWeightsFromParentDensity
public import Oberwolfach.OrdinaryHubSetupFromProfiles

@[expose] public section
/-! Select the fixed fractional parent triangles before choosing later
balance parameters or sampling; they work for every displayed setup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
set_option synthInstance.maxSize 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_inner_hub_setup_before_sampling
    (α : ℝ) (hα : 0<α) :
    ∃ cLo cHi : ℝ, 0<cLo ∧ 0<cHi ∧ ∃ N : ℕ, 0<N ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (A : Finset V), N≤A.card →
    ∀ (P : SimpleGraph V) (density : ℝ), cycleThreshold 3+α≤density →
      (∀v,density*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
    ∃ weight : OrdinaryCycle (P.induce (A:Set V)) 3→ℝ,
      (∀C,cLo/(A.card:ℝ)≤weight C ∧ weight C≤cHi/(A.card:ℝ)) ∧
      (∀x y,(∑C,if C.val.val.Adj x y then weight C else 0)=if (P.induce (A:Set V)).Adj x y then 1 else 0) ∧
    ∀ (U : Type) [Fintype U] [DecidableEq U] (Z : Finset U) (F : SimpleGraph V)
      (p pR pH e δ ξ L b B η K : ℝ),
      0<A.card → 0<p → p≤1 → p≤pR → pR≤1 → p≤pH → pH≤1 →
      0≤δ → 0≤L → 0≤K →
      (∀v,|pR*(P.neighborFinset v∩A).card-2*pH*Z.card|≤e) →
      pR*(A.card:ℝ)/2≤2*pH*Z.card → 2*pH*Z.card≤2*pR*A.card → e/pR≤δ*A.card →
      (∀v,(F.degree v:ℝ)≤L) → (Fintype.card V:ℝ)≤K*A.card → b≤cLo →
      (4*cHi/p^7)*K^2≤B → ξ+2*δ+12*(3:ℝ)^4*cHi*L/A.card≤η →
      OrdinaryInnerHubWeightSetup P F A weight p pR pH (2*pH*Z.card/pR) δ ξ L cLo cHi b B η K := by
  obtain ⟨cLo,cHi,hcLo,hcHi,N,hN,hweights⟩ := ordinary_inner_triangle_weights_from_parent_density α hα
  refine ⟨cLo,cHi,hcLo,hcHi,N,hN,?_⟩
  intro V _ _ A hA P density hdensity hmin
  obtain ⟨weight,hw,he⟩ := hweights V A hA P density hdensity hmin
  refine ⟨weight,hw,he,?_⟩
  intro U _ _ Z F p pR pH e δ ξ L b B η K hApos hp hp1 hpR hpR1 hpH hpH1 hδ hL hK
    hparent hlo hhi hreg hF hsize hb hB herr
  exact ordinary_hub_setup_from_profiles P F A Z weight density α p pR pH e δ ξ L cLo cHi b B η K
    hApos hp hp1 hpR hpR1 hpH hpH1 hδ hL hcLo hcHi.le hK hdensity hmin hparent hlo hhi hreg hF hw he hsize hb hB herr
end Oberwolfach
