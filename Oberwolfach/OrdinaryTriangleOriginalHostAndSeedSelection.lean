module

public import Oberwolfach.OrdinaryTriangleSharpHostGeometryChoiceAt
public import Oberwolfach.OrdinaryAllowedMatchingSeedScheme
public import Oberwolfach.OrdinaryTriangleReferenceSubmargin

@[expose] public section
/-! The same reduced original-host margin and successor-length cutoff
select the triangle host geometry and both kinds of matching seed weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_original_host_and_seed_selection
    (Allowed:Set ℕ) (hAllowed:Allowed.Nonempty) (hValid:∀s∈Allowed,3≤s) (htri:3∈Allowed)
    (hthreshold:allowedThreshold Allowed<1) (α₀ ρ₀ pstar:ℝ)
    (hα₀:0<α₀) (hρ₀:0<ρ₀) (hpstar:0<pstar) (hpstar1:pstar≤1):
    ∃α:ℝ,0<α ∧ α≤α₀ ∧ ∀(K:ℕ) (θ τ:ℝ),0<θ→0<τ→
      ∃k₀:ℕ,(∀k:ℕ,k₀≤k→OrdinaryAllowedMatchingSeedScheme Allowed K k α θ τ) ∧
        OrdinaryTriangleSharpHostGeometryChoiceAt k₀ α ρ₀ pstar hpstar :=by
  have hhalf:1/2≤allowedThreshold Allowed:=allowedThreshold_half_le hAllowed hValid
  have hbdd:BddAbove (cycleThreshold '' Allowed):=by
    refine ⟨1,?_⟩
    rintro x ⟨s,hs,rfl⟩
    exact cycleThreshold_le_one s
  have htriangle:cycleThreshold 3≤allowedThreshold Allowed:=le_csSup hbdd ⟨3,htri,rfl⟩
  obtain ⟨α,hα,hαsub,hα1,hθmargin⟩:=
    ordinary_triangle_reference_submargin (allowedThreshold Allowed) α₀ hhalf htriangle hthreshold hα₀
  refine ⟨α,hα,hαsub,?_⟩
  intro K θ τ hθ hτ
  obtain ⟨k₀,hweights⟩:=ordinary_allowed_matching_seed_scheme_choice Allowed hAllowed hValid K α θ τ hα hθ hτ
  refine ⟨k₀,hweights,?_⟩
  exact ordinary_triangle_sharp_host_geometry_choice_at k₀ α ρ₀ pstar hα hα1 hρ₀ hpstar hpstar1 hθmargin
end Oberwolfach
