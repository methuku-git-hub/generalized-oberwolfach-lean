module

public import Oberwolfach.LongOrderedEveryClassUniformMatchingClassCap

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_residual_class_cap_choice
    (α lam lamAssign ε δold δlocal vstar:ℝ)
    (hα:0<α) (hε:0<ε) (hlam:lam<lamAssign)
    (hδ:δold<δlocal) (hvstar:0<vstar):
    ∃ξCap:ℝ,0<ξCap ∧ ∀ξPart:ℝ,0≤ξPart→ξPart≤ξCap→
      ξPart≤(2*α)/32 ∧ ξPart/2≤(lamAssign-lam)*ε ∧
      ∀n:ℕ,∀ (inner:ℝ),vstar*(n:ℝ)≤ inner →
        ξPart*(n:ℝ)≤(δlocal-δold)*inner := by
  let ξCap:ℝ:=min ((2*α)/32) (min (2*(lamAssign-lam)*ε) ((δlocal-δold)*vstar))
  have hCap:0<ξCap:=lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨ξCap,hCap,?_⟩
  intro ξPart hξ hbound
  have hαcap:ξPart≤(2*α)/32:=hbound.trans (min_le_left _ _)
  have hrest:ξPart≤min (2*(lamAssign-lam)*ε) ((δlocal-δold)*vstar):=hbound.trans (min_le_right _ _)
  have hLamCap:ξPart≤2*(lamAssign-lam)*ε:=hrest.trans (min_le_left _ _)
  have hδcap:ξPart≤(δlocal-δold)*vstar:=hrest.trans (min_le_right _ _)
  refine ⟨hαcap,by linarith,?_⟩
  intro n inner hinner
  calc
    ξPart*(n:ℝ)≤((δlocal-δold)*vstar)*(n:ℝ):=mul_le_mul_of_nonneg_right hδcap (Nat.cast_nonneg n)
    _=(δlocal-δold)*(vstar*(n:ℝ)):=by ring
    _≤(δlocal-δold)*inner:=mul_le_mul_of_nonneg_left hinner (by linarith)
end Oberwolfach
