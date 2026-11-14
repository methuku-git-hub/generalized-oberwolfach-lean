module

public import Oberwolfach.FirstVortexFlexibleGlobalGeometry
public import Oberwolfach.FirstVortexParentDensityCapHierarchy

@[expose] public section
/-! Fix the parent-density cap and global load scales while leaving the
vortex scale free for the subsequent matching choices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_flexible_parent_cap_hierarchy
    (r:ℕ) (κ α ρ₀ plo klo tstar kstar ζFixed thetaDeep B pstar rho upper:ℝ)
    (hκ:0<κ) (hα:0<α) (hρ₀:0<ρ₀) (hplo:0<plo) (hklo:0<klo)
    (htstar:0<tstar) (hζFixed:0<ζFixed) (hθ:0<thetaDeep)
    (hB:0≤B) (hpstar:0<pstar) (hrho:0<rho) (hupper:0<upper):
    let exactCap:=Classical.choose (marked_vortex_fixed_margin_local_correction_cap r κ α (ρ₀/4) plo klo tstar kstar ζFixed thetaDeep (1:ℝ) B pstar (1:ℝ) (1:ℝ) (1:ℝ)
      hκ hα (by positivity) hplo hklo htstar hζFixed hθ (by norm_num) hB hpstar (by norm_num) (by norm_num) (by norm_num));
    ∃cap δsmall δspoke:ℝ,0<cap ∧ cap≤exactCap ∧ 0<δsmall ∧ 0<δspoke ∧ δsmall≤upper ∧
    (∀(n D:ℕ) (U:Type) [Fintype U] (G:SimpleGraph (Fin n)),
      G.IsRegularOfDegree D→0<n→(n:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity U D→
      (ρ₀/4)*(Fintype.card (Fin n):ℝ)≤Fintype.card U) ∧
    ∀ε:ℝ,0<ε→ε<δsmall/4→
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
  have hExact:0<exactCap:=(Classical.choose_spec (marked_vortex_fixed_margin_local_correction_cap r κ α (ρ₀/4) plo klo tstar kstar ζFixed thetaDeep (1:ℝ) B pstar (1:ℝ) (1:ℝ) (1:ℝ)
    hκ hα (by positivity) hplo hklo htstar hζFixed hθ (by norm_num) hB hpstar (by norm_num) (by norm_num) (by norm_num))).1
  let cap:=exactCap/2
  have hcap:0<cap:=by dsimp [cap];positivity
  have hbound:cap≤exactCap:=by dsimp [cap];linarith
  obtain ⟨δsmall,δspoke,hδ,hspoke,hδupper,hlater⟩:=first_vortex_ordered_geometry_rates cap rho upper hcap hrho hupper
  refine ⟨cap,δsmall,δspoke,hcap,hbound,hδ,hspoke,hδupper,?_,?_⟩
  · intro n D U _ G hreg hn hD hrlo
    simpa only [Fintype.card_fin] using (first_vortex_prescribed_hub_density hreg hn hD ρ₀ hρ₀ hrlo).2
  · intro ε hε hεgap
    refine ⟨first_vortex_flexible_global_geometry δsmall ε hε hεgap,?_⟩
    intro c hc
    obtain ⟨t,ht,_,hrate⟩:=first_vortex_local_chain_rate_choice upper c ε rho hupper hc hε hrho
    obtain ⟨eta,s,heta,hetat,hs,hsupper,hlocal⟩:=hlater t ht
    exact ⟨t,ht,hrate,eta,s,heta,hetat,hs,hsupper,hlocal⟩
end Oberwolfach
