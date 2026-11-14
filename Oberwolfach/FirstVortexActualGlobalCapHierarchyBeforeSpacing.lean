module

public import Oberwolfach.MarkedVortexGlobalTransferCapEarly
public import Oberwolfach.FirstVortexOrderedGeometryHierarchyBeforeSpacing

@[expose] public section
/-! Choose the parent-transfer cap and global scales before the vortex,
local tolerance, and spacing parameter. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_actual_global_cap_hierarchy_before_spacing
    (r:ℕ) (κ₀ α ω plo klo tstar kstar ζFixed thetaDeep B pstar rho upper εcap:ℝ)
    (hκ:0<κ₀) (hα:0<α) (hω:0<ω) (hplo:0<plo) (hklo:0<klo)
    (htstar:0<tstar) (hζFixed:0<ζFixed) (hθ:0<thetaDeep)
    (hB:0≤B) (hpstar:0<pstar) (hrho:0<rho) (hupper:0<upper) (hεcap:0<εcap):
    let cCommon:=Classical.choose (marked_vortex_initial_common_from_parent_record r κ₀ α ω plo klo hκ hα hω hplo hklo)
    let cDeep:=Classical.choose (marked_vortex_initial_deep_from_parent_record r (α/2) tstar kstar ζFixed thetaDeep B pstar hζFixed hθ hB hpstar);
    ∃cap:ℝ,0<cap ∧ cap≤cCommon ∧ cap≤cDeep ∧
      (∀ζ:ℝ,0≤ζ→ζ≤cap→(κ₀/2)/4+33*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))*ζ≤κ₀/4) ∧
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
      ∀ζret ηBalance θ a γ ξPart κ Δ b:ℝ,
        ζret≤s→ηBalance≤s→θ≤s→a≤s→γ≤s→ξPart≤s→κ≤s→Δ≤s→b≤s→
        FirstVortexLocalGeometryRateBounds cap rho tLocal eta δsmall δspoke ζret ηBalance θ a γ ξPart κ Δ b :=by
  intro cCommon cDeep
  obtain ⟨cap,hcap,hcommon,hdeep,hpotential⟩:=marked_vortex_global_transfer_cap_early r κ₀ α ω plo klo tstar kstar ζFixed thetaDeep B pstar
    hκ hα hω hplo hklo htstar hζFixed hθ hB hpstar
  have hh:=first_vortex_ordered_geometry_hierarchy_before_spacing cap rho upper εcap hcap hrho hupper hεcap
  exact ⟨cap,hcap,hcommon,hdeep,hpotential,hh⟩
end Oberwolfach
