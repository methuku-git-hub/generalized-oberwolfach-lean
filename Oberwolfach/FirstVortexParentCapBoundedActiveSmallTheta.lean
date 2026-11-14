module

public import Oberwolfach.FirstVortexBoundedActiveLocalMatchingSmallTheta
public import Oberwolfach.FirstVortexParentDensityCapHierarchy

@[expose] public section
/-! Choose the exact parent-density cap before the vortex, and choose the
canonical local and matching rates only after the active tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_parent_cap_bounded_active_small_theta
    (r:ℕ) (κ αParent ρ₀ plo klo tstar kstar ζFixed thetaDeep B pstar:ℝ)
    (rho upper α δold δlocal δglobal ρmatch extra:ℝ)
    (hκ:0<κ) (hαParent:0<αParent) (hρ₀:0<ρ₀) (hplo:0<plo) (hklo:0<klo)
    (htstar:0<tstar) (hζFixed:0<ζFixed) (hθDeep:0<thetaDeep) (hB:0≤B) (hpstar:0<pstar)
    (hrho:0<rho) (hupper:0<upper) (hα:0<α) (hδold:0<δold) (hgap:δold<δlocal)
    (hδglobal:0<δglobal) (hρmatch:0<ρmatch) (hextra:0<extra):
    let exactCap:=Classical.choose (marked_vortex_fixed_margin_local_correction_cap r κ αParent (ρ₀/4) plo klo tstar kstar ζFixed thetaDeep (1:ℝ) B pstar (1:ℝ) (1:ℝ) (1:ℝ)
      hκ hαParent (by positivity) hplo hklo htstar hζFixed hθDeep (by norm_num) hB hpstar (by norm_num) (by norm_num) (by norm_num));
    ∃globalCap:ℝ,0<globalCap ∧ globalCap≤exactCap ∧ globalCap≤extra ∧
    (∀(n D:ℕ) (U:Type) [Fintype U] (G:SimpleGraph (Fin n)),
      G.IsRegularOfDegree D→0<n→(n:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity U D→
      (ρ₀/4)*(Fintype.card (Fin n):ℝ)≤Fintype.card U) ∧
    ∃δsmall δspoke:ℝ,0<δsmall ∧ 0<δspoke ∧ δsmall≤upper ∧
    ∀ε:ℝ,0<ε→ε<δsmall/4→
    (∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U] (P S Sel Used:SimpleGraph (Fin n))
      (D m:ℕ) (β:ℝ) (Q:Vortex U P D β ε m) (π:Equiv.Perm (Fin n))
      (Req:Fin n→Fin n→Prop) (Pack:Finset (Sym2 (Fin n))),
      let I:=Q.extendedVertices 1
      let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
      let Kplus:=longClassInnerRequiredRepair S Used K I Pack;
      ((I.card:ℝ)≤ε*n) ∧ ∀v,((Kplus.degree v:ℝ)≤δsmall*n/4)) ∧
    ∀cLocal activeBound:ℝ,0<cLocal→0<activeBound→
    ∃active:ℝ,0<active ∧ active≤globalCap ∧ active≤cLocal ∧ active≤activeBound ∧
    ∃tLocal eta s θ lamAssign lam ξCap:ℝ,
      0<tLocal ∧ (17+4/rho)*tLocal≤cLocal*ε/2 ∧
      0<eta ∧ eta≤tLocal ∧ 0<s ∧ s≤upper ∧
      0<θ ∧ θ≤s ∧ 0<lamAssign ∧ lamAssign≤s ∧
      10*θ≤δold ∧ θ≤δold/32 ∧ θ≤1/100 ∧ 10*θ≤δglobal ∧ 10*θ≤δsmall ∧
      8*(θ*ε^2+lamAssign*ε)/((ρmatch/4)/40000)<active*ε/128 ∧
      0<lam ∧ 0<ξCap ∧ lam≤θ ∧ lam≤α/128 ∧ lam≤δold*ε/32 ∧
      (∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρmatch/4)/40000)*θ/4096 ∧
        ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
        ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
          (Q:Vortex U G D β ε mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ)) ∧
      ∀ζret ηBalance θ' a γ ξPart κ' Δ b:ℝ,
        ζret≤s→ηBalance≤s→θ'≤s→a≤s→γ≤s→ξPart≤s→κ'≤s→Δ≤s→b≤s→
        FirstVortexLocalGeometryRateBounds globalCap rho tLocal eta δsmall δspoke ζret ηBalance θ' a γ ξPart κ' Δ b :=by
  intro exactCap
  have hExact:0<exactCap:=(Classical.choose_spec (marked_vortex_fixed_margin_local_correction_cap r κ αParent (ρ₀/4) plo klo tstar kstar ζFixed thetaDeep (1:ℝ) B pstar (1:ℝ) (1:ℝ) (1:ℝ)
    hκ hαParent (by positivity) hplo hklo htstar hζFixed hθDeep (by norm_num) hB hpstar (by norm_num) (by norm_num) (by norm_num))).1
  let globalCap:=min (exactCap/2) (extra/2)
  have hcap:0<globalCap:=by dsimp [globalCap];positivity
  have hbound:globalCap≤exactCap:=by dsimp [globalCap];have hh:=min_le_left (exactCap/2) (extra/2);linarith
  have hextraBound:globalCap≤extra:=by dsimp [globalCap];have hh:=min_le_right (exactCap/2) (extra/2);linarith
  refine ⟨globalCap,hcap,hbound,hextraBound,?_,first_vortex_bounded_active_local_matching_small_theta globalCap rho upper α δold δlocal δglobal ρmatch hcap hrho hupper hα hδold hgap hδglobal hρmatch⟩
  intro n D U _ G hreg hn hD hrlo
  simpa only [Fintype.card_fin] using (first_vortex_prescribed_hub_density hreg hn hD ρ₀ hρ₀ hrlo).2
end Oberwolfach
