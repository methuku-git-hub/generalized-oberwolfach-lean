module

public import Oberwolfach.FirstVortexJointGeometricMatchingChoices

@[expose] public section
/-! Choose the concrete matching rates together with the geometric active
rate once the active tolerance and earlier list scales are fixed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_concrete_rate_choices
    (b ρ₀ δold δlocal δglobal lamList βfinal C₀ εcap active:ℝ)
    (hb:0<b) (hρ:0<ρ₀) (hδold:0<δold) (hgap:δold<δlocal)
    (hδglobal:0<δglobal) (hcap:0<εcap) (hlist:0<lamList)
    (hβfinal:0≤βfinal) (hβbound:βfinal≤lamList/4) (hC:1≤C₀) (hactive:0<active):
    ∃θ αMatch εQ lam lamAssign ξCap:ℝ,
      0<θ ∧ 10*θ≤δold ∧ θ≤δold/32 ∧ θ≤1/100 ∧ 10*θ≤δglobal ∧
      0<αMatch ∧ (2*αMatch)/16≤b ∧
      (2*αMatch)/16≤((ρ₀/4)/40000)*θ/1024 ∧ 2*αMatch≤4*δglobal ∧
      0<εQ ∧ εQ≤εcap ∧ εQ≤δglobal ∧ βfinal+εQ≤lamList ∧
      εQ≤αMatch/1000 ∧ εQ≤(ρ₀/4)/80000 ∧ εQ≤((ρ₀/4)/40000)/8192 ∧
      0<lam ∧ 0<lamAssign ∧ 0<ξCap ∧ lam≤θ ∧ lam≤αMatch/128 ∧
      lam≤δold*εQ/32 ∧ lam<lamAssign ∧
      8*(θ*εQ^2+lamAssign*εQ)/((ρ₀/4)/40000)<active*εQ/128 ∧
      8*((1/2:ℝ)*εQ^2)/((ρ₀/4)/40000)<active*εQ/128 ∧
      ∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρ₀/4)/40000)*θ/4096 ∧
        ξ'/2≤(lamAssign-lam)*εQ ∧ ξ'≤αMatch/32 ∧
        ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
          (Q:Vortex U G D β εQ mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ) :=by
  let θ:ℝ:=min (δold/64) (min (δglobal/20) (1/200))
  have hθ:0<θ:=by dsimp [θ];positivity
  have hθold:θ≤δold/64:=min_le_left _ _
  have hθglobal:θ≤δglobal/20:=(min_le_right _ _).trans (min_le_left _ _)
  have hθone:θ≤1/200:=(min_le_right _ _).trans (min_le_right _ _)
  let eprec:ℝ:=((ρ₀/4)/40000)/8192
  have heprec:0<eprec:=by dsimp [eprec];positivity
  obtain ⟨α,ε,lam,lamAssign,ξCap,hα,hαb,hαθ,hαδ,hε,hεcap,hεδ,hlistBound,hεα,hερ,
    hlam,hAssign,hξ,hlamθ,hlamα,hlamδ,hgapLam,hRate,hgeom,hCap⟩:=
    first_vortex_joint_geometric_matching_choices b ρ₀ θ δold δlocal δglobal lamList βfinal C₀ (min εcap eprec) active
      hb hρ hθ hδold hgap hδglobal (lt_min hcap heprec) hlist hβfinal hβbound hC hactive
  have hεα':ε≤α/1000:=by
    have hden:α/(1000*C₀)≤α/1000:=by
      apply div_le_div_of_nonneg_left hα.le (by norm_num) (by nlinarith)
    exact hεα.trans hden
  exact ⟨θ,α,ε,lam,lamAssign,ξCap,hθ,by linarith,by linarith,by linarith,by linarith,
    hα,hαb,hαθ,hαδ,hε,hεcap.trans (min_le_left _ _),hεδ,hlistBound,hεα',hερ,
    hεcap.trans (min_le_right _ _),hlam,hAssign,hξ,hlamθ,hlamα,hlamδ,hgapLam,hRate,hgeom,hCap⟩
end Oberwolfach
