module

public import Oberwolfach.FirstVortexEarlyHostPreparedCap

@[expose] public section
/-! The late sampling and edit tolerances can be chosen after all earlier
    caps, including arbitrary additional positive caps, are fixed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_prepared_rate_choices
    (K:ℕ) (lam θ ξCap epsCap ξPrepCap ξPartCap:ℝ)
    (hK:0<K) (hlam:0<lam) (hθ:0<θ) (hξ:0<ξCap)
    (hepsCap:0<epsCap) (hprepCap:0<ξPrepCap) (hpartCap:0<ξPartCap):
    ∃eps ξPrep ξPart:ℝ,
      0<eps ∧ eps≤1 ∧ eps≤epsCap ∧
      3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
      0<ξPrep ∧ ξPrep≤ξPrepCap ∧ 4*ξPrep≤eps/2 ∧
      0<ξPart ∧ ξPart≤ξCap ∧ ξPart≤ξPartCap :=by
  have hKR:(0:ℝ)<K:=by exact_mod_cast hK
  let B:ℝ:=lam*θ/(600*(K:ℝ)^2)
  have hB:0<B:=by dsimp [B];positivity
  let eps:ℝ:=min (1/2) (min B epsCap)
  have heps:0<eps:=by dsimp [eps];positivity
  have heps1:eps≤1:=by have h:=min_le_left (1/2:ℝ) (min B epsCap);dsimp [eps];linarith
  have hepsB:eps≤B:=(min_le_right _ _).trans (min_le_left _ _)
  have hepsCap':eps≤epsCap:=(min_le_right _ _).trans (min_le_right _ _)
  have hRate:3*eps≤lam*(θ/(100*(K:ℝ)^2)):=by
    have heq:lam*(θ/(100*(K:ℝ)^2))=6*B:=by dsimp [B];ring
    rw [heq]
    linarith
  let ξPrep:ℝ:=min (eps/16) ξPrepCap
  let ξPart:ℝ:=min ξCap ξPartCap
  have hprep:0<ξPrep:=by dsimp [ξPrep];positivity
  have hpart:0<ξPart:=by dsimp [ξPart];positivity
  have hprepRate:4*ξPrep≤eps/2:=by
    have h:=min_le_left (eps/16) ξPrepCap
    dsimp [ξPrep]
    linarith
  exact ⟨eps,ξPrep,ξPart,heps,heps1,hepsCap',hRate,hprep,min_le_right _ _,hprepRate,hpart,min_le_left _ _,min_le_right _ _⟩
end Oberwolfach
