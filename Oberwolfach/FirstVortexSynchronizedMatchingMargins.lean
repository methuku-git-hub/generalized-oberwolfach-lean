module

public import Oberwolfach.LongFirstVortexMatchingScaleActual
public import Oberwolfach.LongResidualVortexClassCapChoice
public import Oberwolfach.LongOrderedMatchingResidualRates

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_synchronized_matching_margins
    (K d:ℕ) (hK:0<K) (hd:0<d) (θ lam lamAssign ε δold δlocal αMatch eps:ℝ)
    (hθ:0<θ) (hlam:0<lam) (hε:0<ε) (hα:0<αMatch) (heps:0<eps)
    (hδ:0≤δold) (hδ1:δold≤1) (hδgap:δold<δlocal) (hlamAssign:lam<lamAssign)
    (hlamδ:lam≤δold*ε/32) (hinv:1/(d:ℝ)≤θ/1024):
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))
    0≤a ∧ 0≤γ ∧ a≤lam/(10*d) ∧ γ≤lam/(10*d) ∧ γ≤lam/10 ∧ γ≤eps ∧ γ≤1/2 ∧
    ∃ξCap:ℝ,0<ξCap ∧ ∀ξPart:ℝ,0≤ξPart→ξPart≤ξCap→
      ξPart≤(2*αMatch)/32 ∧ ξPart/2≤(lamAssign-lam)*ε ∧
      ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D m:ℕ) (β:ℝ)
        (Q:Vortex U G D β ε m),0<m→
        ξPart*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ) ∧
        max a γ*(n:ℝ)≤(θ/4096)*(Q.extendedVertices 1).card :=by
  intro a γ
  have hRates:=long_ordered_matching_residual_rates K d hK hd θ lam eps hθ hlam heps
  obtain ⟨ha,hγ,haLam,hγLam,hγ10,hγeps,hγhalf⟩:=hRates
  refine ⟨ha,hγ,haLam,hγLam,hγ10,hγeps,hγhalf,?_⟩
  obtain ⟨ξCap,hCap,hMargins⟩:=long_residual_vortex_class_cap_choice αMatch lam lamAssign ε δold δlocal hα hε hlamAssign hδgap
  refine ⟨ξCap,hCap,?_⟩
  intro ξPart hξ hξcap
  obtain ⟨hdeg,hedges,hinner⟩:=hMargins ξPart hξ hξcap
  refine ⟨hdeg,hedges,?_⟩
  intro n U _ G D m β Q hm
  exact ⟨hinner n U G D m β Q hm,
    long_first_vortex_matching_scale_actual d θ lam ε δold a γ n hd hθ hlam hε hδ hδ1 hlamδ hinv haLam hγLam U G D m β Q hm⟩
end Oberwolfach
