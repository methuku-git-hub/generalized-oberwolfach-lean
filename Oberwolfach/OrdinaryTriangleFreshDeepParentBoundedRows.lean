module

public import Oberwolfach.OrdinaryTriangleFreshFromInnerCleanup
public import Oberwolfach.OrdinaryDeepParentIngredients

@[expose] public section
/-! Existing same-sample deep-parent ingredients can feed the new inner
triangle factor construction. The unused ambient-scale constants remain
independent parameters of the input, not bounds on the new tolerance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_fresh_from_deep_parent_inner_bounded_rows
    (κe pmin bHub BHub:ℝ) (hκ:0<κe) (hpmin:0<pmin) (hpmin1:pmin≤1)
    (hb:0<bHub) (hB:0≤BHub):
    ∃εfactor ηhub ηend ζ εrows:ℝ,0<εfactor ∧ 0<ηhub ∧ 0<ηend ∧ 0<ζ ∧ 0<εrows ∧
      εrows≤min (pmin^4/16) (pmin^3/2) ∧
    ∀(b₀:ℕ) (p:ℝ) (hp:0<p) (hp1:p≤1) (εsup:ℝ) (hsup:0<εsup) (q:ℕ),∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
      (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
      (weight:V→Sym2 (V⊕U)→ℝ) (γold κold bold Bold εold pR pH density tR tH tP L Ledit βe βh δ K:ℝ)
      (σ:RawWheelOutcome V U Γ Color),
    N≤A.card→Fintype.card {v:V // v∉A}≤A.card^2→Fintype.card {u:U // u∉Z}≤A.card^2→
    OrdinaryDeepParentIngredients P Q F H A Z π d j s weight γold κold bold Bold εold ηend κe pmin
      pR pH density tR tH L Ledit βe βh δ εrows tP K σ→
    OrdinaryMixedHubWeightsInnerScale 2 bHub BHub ηhub Q F H A Z→
    (∀v,F.degree v≤b₀)→L≤εfactor*A.card→
    1-1/(A.card:ℝ)^q-1/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (OrdinaryTriangleFreshFactorSample Q (spanningRestriction Q A) F H
          (fun v u=>H v u∧v∈A∧u∈Z) A Z p ζ εsup):=by
  obtain ⟨εfactor,ηhub,ηend,ζ,εrows0,hε,hηh,hηe,hζ,hrows0,hfresh⟩:=
    ordinary_triangle_fresh_from_inner_cleanup κe pmin bHub BHub hκ hpmin hpmin1 hb hB
  let εrows:ℝ:=min εrows0 (min (pmin^4/16) (pmin^3/2))/2
  have hrows:0<εrows:=by dsimp [εrows];positivity
  have hrowsOld:εrows≤εrows0:=by
    have hh:=min_le_left εrows0 (min (pmin^4/16) (pmin^3/2))
    dsimp [εrows];linarith
  have hrowsGeom:εrows≤min (pmin^4/16) (pmin^3/2):=by
    have hh:=min_le_right εrows0 (min (pmin^4/16) (pmin^3/2))
    have hz:0≤min (pmin^4/16) (pmin^3/2):=by positivity
    dsimp [εrows];linarith
  refine ⟨εfactor,ηhub,ηend,ζ,εrows,hε,hηh,hηe,hζ,hrows,hrowsGeom,?_⟩
  intro b₀ p hp hp1 εsup hsup q
  obtain ⟨N,hN⟩:=hfresh b₀ p hp hp1 εsup hsup q
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P Q F H A Z π d j s weight γold κold bold Bold εold pR pH density tR tH tP
    L Ledit βe βh δ K σ hn hJv hJu inputs hub hF hL
  have hrow:=inputs.row_margin.trans (mul_le_mul_of_nonneg_right hrowsOld (Nat.cast_nonneg A.card))
  have hindex:=inputs.index_margin.trans (mul_le_mul_of_nonneg_right hrowsOld (Nat.cast_nonneg Z.card))
  exact hN V U Γ Color P Q F H A Z π d j s weight pR pH density tR tH tP L Ledit βe βh δ σ
    hn hJv hJu inputs.profile inputs.deep inputs.parent inputs.endpoint_event inputs.geom hub
    inputs.geom.rim_lower inputs.geom.spoke_lower inputs.density_lower inputs.geom.conflict_nonneg
    inputs.geom.edit_nonneg hF inputs.conflict_degree hrow hindex inputs.conflict_inner
    hL inputs.endpoint_error inputs.parent_degree
end Oberwolfach
