module

public import Oberwolfach.FirstVortexMatchingScalePositive

@[expose] public section
/-! Choose the class-edit cap and matching parameter from the already fixed
inner-vortex scale and assignment allowance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_matching_class_cap_choice
    (α lamAssign ε δold δlocal θ ρ₀:ℝ)
    (hα:0<α) (hAssign:0<lamAssign) (hε:0<ε) (hδ:0<δold)
    (hgap:δold<δlocal) (hθ:0<θ) (hρ:0<ρ₀):
    ∃lam ξCap:ℝ,0<lam ∧ 0<ξCap ∧ lam≤θ ∧ lam≤α/128 ∧ lam≤δold*ε/32 ∧
      ∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρ₀/4)/40000)*θ/4096 ∧
        ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
        ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
          (Q:Vortex U G D β ε mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ) :=by
  let B:ℝ:=((ρ₀/4)/40000)*θ/4096
  have hB:0<B:=by dsimp [B];positivity
  let L₁:=min (B/4) (lamAssign/4)
  let L₂:=min θ (min (α/128) (δold*ε/32))
  let X₁:=min (B/4) (lamAssign*ε/4)
  let X₂:=min (α/32) ((δlocal-δold)*ε/4)
  let lam:ℝ:=min L₁ L₂/2
  let ξCap:ℝ:=min X₁ X₂/2
  have hlam:0<lam:=by dsimp [lam,L₁,L₂];positivity
  have hξ:0<ξCap:=by dsimp [ξCap,X₁,X₂];positivity
  have hL₁:min L₁ L₂≤L₁:=min_le_left _ _
  have hL₂:min L₁ L₂≤L₂:=min_le_right _ _
  have hX₁:min X₁ X₂≤X₁:=min_le_left _ _
  have hX₂:min X₁ X₂≤X₂:=min_le_right _ _
  have hlamB:lam≤B/4:=by
    have h:=min_le_left (B/4) (lamAssign/4)
    change min L₁ L₂/2≤B/4
    dsimp [L₁] at hL₁
    linarith
  have hlamAssign:lam≤lamAssign/4:=by
    have h:=min_le_right (B/4) (lamAssign/4)
    change min L₁ L₂/2≤lamAssign/4
    dsimp [L₁] at hL₁
    linarith
  have hlamθ:lam≤θ:=by
    have h:=min_le_left θ (min (α/128) (δold*ε/32))
    change min L₁ L₂/2≤θ
    dsimp [L₂] at hL₂
    linarith
  have hlamα:lam≤α/128:=by
    have h: L₂≤α/128:=(min_le_right θ _).trans (min_le_left _ _)
    change min L₁ L₂/2≤α/128
    linarith
  have hlamδ:lam≤δold*ε/32:=by
    have h:L₂≤δold*ε/32:=(min_le_right θ _).trans (min_le_right _ _)
    change min L₁ L₂/2≤δold*ε/32
    have hp:0<δold*ε:=mul_pos hδ hε
    linarith
  have hξB:ξCap≤B/4:=by
    have h:X₁≤B/4:=min_le_left _ _
    change min X₁ X₂/2≤B/4
    linarith
  have hξAssign:ξCap≤lamAssign*ε/4:=by
    have h:X₁≤lamAssign*ε/4:=min_le_right _ _
    change min X₁ X₂/2≤lamAssign*ε/4
    have hp:0<lamAssign*ε:=mul_pos hAssign hε
    linarith
  have hξα:ξCap≤α/32:=by
    have h:X₂≤α/32:=min_le_left _ _
    change min X₁ X₂/2≤α/32
    linarith
  have hξgap:ξCap≤(δlocal-δold)*ε/4:=by
    have h:X₂≤(δlocal-δold)*ε/4:=min_le_right _ _
    change min X₁ X₂/2≤(δlocal-δold)*ε/4
    have hp:0<(δlocal-δold)*ε:=by positivity
    linarith
  refine ⟨lam,ξCap,hlam,hξ,hlamθ,hlamα,hlamδ,?_⟩
  intro ξ' hξ'
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [B] at hlamB hξB;linarith
  · have hh:=mul_le_mul_of_nonneg_right hlamAssign hε.le
    nlinarith
  · linarith
  · intro n U _ G D mm β Q hmm
    have hsize:=Q.first_inner_vertex_size_lower_of_positive_terminal_size hε hmm
    have hGap:0≤δlocal-δold:=by linarith
    have hh:=mul_le_mul_of_nonneg_left hsize hGap
    have hn:(0:ℝ)≤n:=Nat.cast_nonneg _
    have hξn:=mul_le_mul_of_nonneg_right hξ' hn
    have hcapn:=mul_le_mul_of_nonneg_right hξgap hn
    have hprod:0≤(δlocal-δold)*ε*(n:ℝ):=by positivity
    simp only [Fintype.card_fin] at hh
    nlinarith
end Oberwolfach
