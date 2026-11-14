module

public import Oberwolfach.OrdinaryTriangleInnerScaledConditions

@[expose] public section
/-! The scaled triangle finish conditions follow from the actual cleanup
profile and two-step sample, with a linear inner-domain margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_scaled_conditions_from_inner_cleanup
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (κ pmin pR pH density tR tH L Ledit βe βh δ εrows:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH Ledit βe βh s j σ)
    (deep:RawOrdinaryRows P π d 3 A pR s j tR σ)
    (geom:EndpointPhysicalEditedConditions P Q F H A B Aᶜ π d j κ pmin pR pH L Ledit δ σ)
    (hpmin1:pmin≤1) (hdensity:(3/4:ℝ)≤density)
    (hrow:tR+4*Ledit≤εrows*A.card) (hindex:tH+3*Ledit≤εrows*B.card)
    (hLA:L≤(A.card:ℝ)/24) (hεrows:εrows≤min (pmin^4/16) (pmin^3/2))
    (hF:∀v,(F.degree v:ℝ)≤L)
    (hdeg:∀x∉A,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ))
    (εv p εsup τ ν η ell ζ:ℝ) (hεv:0<εv) (hp:0<p) (hp1:p≤1) (hτ:0≤τ) (hζ:0<ζ)
    (hsize:(εv/4)*Fintype.card (V⊕U)≤(A.card:ℝ))
    (hε:εsup≤p^2/4) (hsupport:τ+ν≤p^2/4):
    let γ:ℝ:=min (pmin^4/32) (endpointCountCoefficient pmin κ/4);
    let θ:ℝ:=ζ*(γ/4)*εv;
    τ+ν+ell≤θ*p/4→ν+η≤θ*p/4→p≤4*θ→20*Real.sqrt (2*p)≤θ/2→
    2≤θ*p*Fintype.card (V⊕U)/4→
    OrdinaryTriangleRootFirstScaledConditions Q H A B p εsup τ ν η ell ((γ/4)*εv) ζ:=by
  intro γ θ hclass hblock hpκ hsqrt horder
  have hh:=ordinary_triangle_inner_class_margins P Q F H A B π d j s κ pmin pR pH density tR tH L Ledit
    βe βh δ εrows σ profile deep geom hpmin1 hdensity hrow hindex hLA hεrows hF hdeg
  dsimp only at hh
  obtain ⟨hγ,hκambient,hY,hZ⟩:=hh
  have hn:0<(Fintype.card (V⊕U):ℝ):=by
    have hA:0<Fintype.card V:=Fintype.card_pos_iff.mpr ⟨(Finset.card_pos.mp geom.row_pos).choose⟩
    have hAV:Fintype.card V≤Fintype.card (V⊕U):=Fintype.card_le_of_injective Sum.inl Sum.inl_injective
    exact_mod_cast (show 0<Fintype.card (V⊕U) by omega)
  have heq:(γ*A.card/Fintype.card (V⊕U))*Fintype.card (V⊕U)=γ*A.card:=
    div_mul_cancel₀ _ (ne_of_gt hn)
  change ∀u:{u:U // u∉B},(γ*A.card/Fintype.card (V⊕U))*Fintype.card (V⊕U)≤((ordinaryBoundaryHubSet H B A u).card:ℝ) at hY
  change ∀v:{v:V // v∉A},(γ*A.card/Fintype.card (V⊕U))*Fintype.card (V⊕U)≤((ordinaryBoundaryRowSet H A B v).card:ℝ) at hZ
  have hY':∀u:{u:U // u∉B},γ*A.card≤((ordinaryBoundaryHubSet H B A u).card:ℝ):=by
    intro u
    simpa only [heq] using hY u
  have hZ':∀v:{v:V // v∉A},γ*A.card≤((ordinaryBoundaryRowSet H A B v).card:ℝ):=by
    intro v
    simpa only [heq] using hZ v
  exact ordinary_triangle_inner_scaled_conditions Q H A B γ εv p εsup τ ν η ell ζ
    hγ hεv hp hp1 hτ hζ hsize hY' hZ' hε hsupport hclass hblock hpκ hsqrt horder
end Oberwolfach
