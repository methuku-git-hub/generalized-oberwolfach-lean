module

public import Oberwolfach.FirstVortexExactTwoScaleGlobalCapHierarchy
public import Oberwolfach.FirstVortexPrescribedHubDensity

@[expose] public section
/-! The cap for the parent-level transfer is chosen using the actual host
hub-density lower bound, independently of the later inner-level density. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_parent_density_cap_hierarchy
    (r:ℕ) (κ α ρ₀ plo klo tstar kstar ζFixed thetaDeep B pstar rho upper εcap:ℝ)
    (hκ:0<κ) (hα:0<α) (hρ₀:0<ρ₀) (hplo:0<plo) (hklo:0<klo)
    (htstar:0<tstar) (hζFixed:0<ζFixed) (hθ:0<thetaDeep)
    (hB:0≤B) (hpstar:0<pstar) (hrho:0<rho) (hupper:0<upper) (hεcap:0<εcap):
    let exactCap:=Classical.choose (marked_vortex_fixed_margin_local_correction_cap r κ α (ρ₀/4) plo klo tstar kstar ζFixed thetaDeep (1:ℝ) B pstar (1:ℝ) (1:ℝ) (1:ℝ)
      hκ hα (by positivity) hplo hklo htstar hζFixed hθ (by norm_num) hB hpstar (by norm_num) (by norm_num) (by norm_num));
    ∃cap:ℝ,0<cap ∧ cap≤exactCap ∧
    (∀(n D:ℕ) (U:Type) [Fintype U] (G:SimpleGraph (Fin n)),
      G.IsRegularOfDegree D→0<n→(n:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity U D→
      (ρ₀/4)*(Fintype.card (Fin n):ℝ)≤Fintype.card U) ∧
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
  obtain ⟨cap,hcap,hbound,hgeometry⟩:=first_vortex_exact_two_scale_global_cap_hierarchy r κ α (ρ₀/4) plo klo tstar kstar ζFixed thetaDeep B pstar rho upper εcap
    hκ hα (by positivity) hplo hklo htstar hζFixed hθ hB hpstar hrho hupper hεcap
  refine ⟨cap,hcap,hbound,?_,hgeometry⟩
  intro n D U _ G hreg hn hD hrlo
  simpa only [Fintype.card_fin] using (first_vortex_prescribed_hub_density hreg hn hD ρ₀ hρ₀ hrlo).2
end Oberwolfach
