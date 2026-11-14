module

public import Mathlib.Tactic

@[expose] public section
/-! The ambient deeper-balance cap and the relative inner-change cap can be
chosen independently of the eventual vortex scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_localized_balance_budget_choice
    (m:ℕ) (etaBal x:ℝ) (hη:0<etaBal) (hx:0<x):
    ∃c ζmax:ℝ,0<c ∧ 0<ζmax ∧ ((m+4:ℕ):ℝ)*ζmax≤x/4 ∧
    ∀(V:Type) [Fintype V] [DecidableEq V] (A:Finset V),
      2*(c*A.card)+((m+2:ℕ):ℝ)*(c*A.card)≤
        min ((x/4)*Fintype.card V) ((etaBal/2)*A.card) :=by
  let M:ℝ:=(m+4:ℕ)
  have hM:0<M:=by dsimp [M]; positivity
  let c:ℝ:=min (x/(16*M)) (etaBal/(16*M))
  let ζmax:ℝ:=x/(8*M)
  have hc:0<c:=by dsimp [c];positivity
  have hz:0<ζmax:=by dsimp [ζmax];positivity
  have hcx:M*c≤x/16:=by
    have hh:=mul_le_mul_of_nonneg_left (min_le_left (x/(16*M)) (etaBal/(16*M))) hM.le
    have heq:M*(x/(16*M))=x/16:=by field_simp
    dsimp only [c]
    linarith
  have hcη:M*c≤etaBal/16:=by
    have hh:=mul_le_mul_of_nonneg_left (min_le_right (x/(16*M)) (etaBal/(16*M))) hM.le
    have heq:M*(etaBal/(16*M))=etaBal/16:=by field_simp
    dsimp only [c]
    linarith
  have hzcap:M*ζmax≤x/4:=by dsimp [ζmax]; field_simp; linarith
  refine ⟨c,ζmax,hc,hz,by simpa only [M] using hzcap,?_⟩
  intro V _ _ A
  have hA:(0:ℝ)≤A.card:=Nat.cast_nonneg _
  have hcard:(A.card:ℝ)≤Fintype.card V:=by exact_mod_cast Finset.card_le_univ A
  have h1:=mul_le_mul_of_nonneg_right hcx hA
  have h2:=mul_le_mul_of_nonneg_right hcη hA
  have h3:=mul_le_mul_of_nonneg_left hcard (show 0≤x/16 by positivity)
  have heq:2*(c*A.card)+((m+2:ℕ):ℝ)*(c*A.card)=M*c*A.card:=by dsimp [M];push_cast;ring
  rw [heq]
  apply le_min <;> nlinarith [mul_nonneg hx.le hA,mul_nonneg hη.le hA]
end Oberwolfach
