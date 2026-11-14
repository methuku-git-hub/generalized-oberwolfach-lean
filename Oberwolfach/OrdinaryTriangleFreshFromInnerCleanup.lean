module

public import Oberwolfach.OrdinaryTriangleFreshSampleFromInner
public import Oberwolfach.OrdinaryTriangleNormalizedHubProbabilityFromCleanup
public import Oberwolfach.EndpointTriangleInnerProbabilityFromCleanup

@[expose] public section
/-! Choose the triangle factor constants from the original lower bounds,
then produce the fresh event from one fixed cleanup outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_fresh_from_inner_cleanup
    (κ pmin b Bweight:ℝ) (hκ:0<κ) (hpmin:0<pmin) (hpmin1:pmin≤1)
    (hb:0<b) (hB:0≤Bweight):
    ∃εfactor ηhub ηend ζ εrows:ℝ,0<εfactor ∧ 0<ηhub ∧ 0<ηend ∧ 0<ζ ∧ 0<εrows ∧
    ∀(b₀:ℕ) (p:ℝ) (hp:0<p) (hp1:p≤1) (εsup:ℝ) (hsup:0<εsup) (q:ℕ),∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
      (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
      (weight:V→Sym2 (V⊕U)→ℝ) (pR pH density tR tH tP L Ledit βe βh δ:ℝ)
      (σ:RawWheelOutcome V U Γ Color),
    N≤A.card→Fintype.card {v:V // v∉A}≤A.card^2→Fintype.card {u:U // u∉Z}≤A.card^2→
    OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ→
    RawOrdinaryRows P π d 3 A pR s j tR σ→
    EndpointPhysicalParentWeights P A Aᶜ weight→
    EndpointPhysicalPotentialEvent P F A Z Aᶜ π d j weight pR pH tP σ→
    EndpointPhysicalEditedConditions P Q F H A Z Aᶜ π d j κ pmin pR pH L Ledit δ σ→
    OrdinaryMixedHubWeightsInnerScale 2 b Bweight ηhub Q F H A Z→
    pmin≤pR→pmin≤pH→(3/4:ℝ)≤density→0≤L→0≤Ledit→
    (∀v,F.degree v≤b₀)→(∀v,(F.degree v:ℝ)≤L)→
    tR+4*Ledit≤εrows*A.card→tH+3*Ledit≤εrows*Z.card→
    L≤(A.card:ℝ)/24→L≤εfactor*A.card→
    δ+(2*40+(1+2*40)/(2*κ*pmin))*L/A.card+
      (tP+10*(40/(κ*pmin^5))*Ledit/A.card)≤ηend→
    (∀x∉A,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ))→
    1-1/(A.card:ℝ)^q-1/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (OrdinaryTriangleFreshFactorSample Q (spanningRestriction Q A) F H
          (fun v u=>H v u∧v∈A∧u∈Z) A Z p ζ εsup):=by
  obtain ⟨εh,ηh,ζh,hεh,hηh,hζh,hhub⟩:=
    ordinary_triangle_normalized_hub_probability_from_cleanup pmin b Bweight hpmin hpmin1 hb hB
  obtain ⟨εe,ηe,ζe,εr,hεe,hηe,hζe,hεr,hend⟩:=
    endpoint_triangle_inner_probability_from_cleanup κ pmin hκ hpmin
  refine ⟨εe,ηh,ηe,min ζh ζe,min εh εr,hεe,hηh,hηe,lt_min hζh hζe,lt_min hεh hεr,?_⟩
  intro b₀ p hp hp1 εsup hsup q
  obtain ⟨Nh,hNh⟩:=hhub b₀ (q+1) p hp hp1
  obtain ⟨Ne,hNe⟩:=hend p hp hp1 (q+1)
  obtain ⟨Nf,hNf⟩:=ordinary_triangle_fresh_sample_from_inner p εsup hp hp1 hsup q
  refine ⟨max Nh (max Ne Nf),?_⟩
  intro V U Γ Color _ _ _ _ _ _ P Q F H A Z π d j s weight pR pH density tR tH tP L Ledit βe βh δ σ
    hn hJv hJu profile deep parent event geom hubdata hpR hpH hdensity hL hLedit hF hFL hrow hindex hLA hLfactor herr hdeg
  have hA:A.Nonempty:=Finset.card_pos.mp geom.row_pos
  have hrowh:tR+4*Ledit≤εh*A.card:=hrow.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have hrowe:tR+4*Ledit≤εr*A.card:=hrow.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _))
  have hindexe:tH+3*Ledit≤εr*Z.card:=hindex.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _))
  have hh:=hNh V U Γ Color P Q F H A Z π d j s pR pH density tR tH L Ledit βe βh σ
    profile deep hA (by omega) hJu hpR hpH hdensity hL hLedit hLA hF hFL hrowh hubdata
  have he:=hNe V U Γ Color P Q F H A Z π d j s weight pR pH density tR tH tP L Ledit βe βh δ σ
    (by omega) hJv profile deep parent event geom hrowe hindexe hLA hLfactor herr hdeg
  exact hNf V U Q F H A Z ζh ζe (by omega) hh he
end Oberwolfach
