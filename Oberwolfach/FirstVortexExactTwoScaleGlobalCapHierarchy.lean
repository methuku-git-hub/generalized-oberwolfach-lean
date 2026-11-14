module

public import Oberwolfach.MarkedVortexFixedMarginLocalCorrectionCap
public import Oberwolfach.FirstVortexOrderedGeometryHierarchyBeforeSpacing

@[expose] public section
/-! Fix the exact global cap used by the two-scale chain before the vortex
scale, the later local tolerance and the spacing parameter. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_exact_two_scale_global_cap_hierarchy
    (r:ℕ) (κ α ω plo klo tstar kstar ζFixed thetaDeep B pstar rho upper εcap:ℝ)
    (hκ:0<κ) (hα:0<α) (hω:0<ω) (hplo:0<plo) (hklo:0<klo)
    (htstar:0<tstar) (hζFixed:0<ζFixed) (hθ:0<thetaDeep)
    (hB:0≤B) (hpstar:0<pstar) (hrho:0<rho) (hupper:0<upper) (hεcap:0<εcap):
    let exactCap:=Classical.choose (marked_vortex_fixed_margin_local_correction_cap r κ α ω plo klo tstar kstar ζFixed thetaDeep (1:ℝ) B pstar (1:ℝ) (1:ℝ) (1:ℝ)
      hκ hα hω hplo hklo htstar hζFixed hθ (by norm_num) hB hpstar (by norm_num) (by norm_num) (by norm_num));
    ∃cap:ℝ,0<cap ∧ cap≤exactCap ∧
    ∃δsmall δspoke ε:ℝ,0<δsmall ∧ 0<δspoke ∧ δsmall≤upper ∧
      0<ε ∧ ε≤εcap ∧ ε<δsmall/4 ∧
    (∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U] (P S Sel Used:SimpleGraph (Fin n))
      (D m:ℕ) (β:ℝ) (Q:Vortex U P D β ε m) (π:Equiv.Perm (Fin n))
      (Req:Fin n→Fin n→Prop) (Pack:Finset (Sym2 (Fin n))),
      let I:=Q.extendedVertices 1
      let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
      let Kplus:=longClassInnerRequiredRepair S Used K I Pack;
      ((I.card:ℝ)≤ε*n) ∧ ∀v,((Kplus.degree v:ℝ)≤δsmall*n/4)) ∧
    ∀c:ℝ,0<c→∃tLocal:ℝ,0<tLocal ∧ (17+4/rho)*tLocal≤c*ε/2 ∧
      ∃eta s:ℝ,0<eta ∧ eta≤tLocal ∧ 0<s ∧ s≤upper ∧
      ∀ζret ηBalance θ a γ ξPart κ' Δ b:ℝ,
        ζret≤s→ηBalance≤s→θ≤s→a≤s→γ≤s→ξPart≤s→κ'≤s→Δ≤s→b≤s→
        FirstVortexLocalGeometryRateBounds cap rho tLocal eta δsmall δspoke ζret ηBalance θ a γ ξPart κ' Δ b :=by
  intro exactCap
  have hExact:0<exactCap:=(Classical.choose_spec (marked_vortex_fixed_margin_local_correction_cap r κ α ω plo klo tstar kstar ζFixed thetaDeep (1:ℝ) B pstar (1:ℝ) (1:ℝ) (1:ℝ)
    hκ hα hω hplo hklo htstar hζFixed hθ (by norm_num) hB hpstar (by norm_num) (by norm_num) (by norm_num))).1
  let cap:=exactCap/2
  have hcap:0<cap:=by dsimp [cap];positivity
  have hbound:cap≤exactCap:=by dsimp [cap];linarith
  exact ⟨cap,hcap,hbound,first_vortex_ordered_geometry_hierarchy_before_spacing cap rho upper εcap hcap hrho hupper hεcap⟩
end Oberwolfach
