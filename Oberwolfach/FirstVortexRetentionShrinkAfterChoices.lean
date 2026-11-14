module

public import Oberwolfach.FirstVortexOrderedAllHubRetention

@[expose] public section
/-! Later positive tolerances may shrink the global retention error while
preserving both the residual-size bound and every-hub local control. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_restriction_good_mono_tolerance
    {V U Γ Color I:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype I]
    [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
    (S:I→Finset V) (T:I→Finset U) (ζ₁ ζ₂:ℝ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g) t)
    (hζ:ζ₁≤ζ₂) (hgood:RetainedRestrictionGood π d σ g t S T ζ₁ J):
    RetainedRestrictionGood π d σ g t S T ζ₂ J :=by
  intro i
  constructor
  · intro u
    exact (hgood i).1 u |>.trans (mul_le_mul_of_nonneg_right hζ (by positivity))
  · intro x
    exact (hgood i).2 x |>.trans (mul_le_mul_of_nonneg_right hζ (by positivity))

theorem first_vortex_retention_shrink_after_choices
    (ε θ ζglobal ζlocal:ℝ) (m d Nret:ℕ) (hglobal:0<ζglobal)
    (hNret:∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/((m:ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζglobal*n)+errOrd≤4*θ*n)
    (hRet:∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
      ∀(G:SimpleGraph V) (D mm:ℕ) (β:ℝ) (Q:Vortex U G D β ε mm) (hmm:0<mm)
      (π:Equiv.Perm V) (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
      (J:StartRetentionOutcome (rawStartHubSet π d σ g) t),
      RetainedRestrictionGood π d σ g t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζglobal J→
      RetainedRestrictionLocalGood π d σ g t (Q.extendedVertices 1) Finset.univ ζlocal J):
    ∀upper:ℝ,0<upper→∃ζ:ℝ,0<ζ ∧ ζ≤upper ∧ ζ≤ζglobal ∧
      (∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
        q≤1/((m:ℝ)+1)→errOrd≤θ*n→
        (n:ℝ)*q/d+(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n)+errOrd≤4*θ*n) ∧
      ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
        [LinearOrder V] [DecidableEq U],
      ∀(G:SimpleGraph V) (D mm:ℕ) (β:ℝ) (Q:Vortex U G D β ε mm) (hmm:0<mm)
        (π:Equiv.Perm V) (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
        (J:StartRetentionOutcome (rawStartHubSet π d σ g) t),
      RetainedRestrictionGood π d σ g t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ J→
      RetainedRestrictionLocalGood π d σ g t (Q.extendedVertices 1) Finset.univ ζlocal J :=by
  intro upper hupper
  let ζ:=min upper ζglobal/2
  have hζ:0<ζ:=by dsimp [ζ]; positivity
  have hζup:ζ≤upper:=by dsimp [ζ]; have :=min_le_left upper ζglobal; linarith
  have hζglobal:ζ≤ζglobal:=by dsimp [ζ]; have :=min_le_right upper ζglobal; linarith
  refine ⟨ζ,hζ,hζup,hζglobal,?_,?_⟩
  · intro n hn q err hq herr
    have hh:=hNret n hn q err hq herr
    have hm:=mul_le_mul_of_nonneg_right hζglobal (show (0:ℝ)≤n by positivity)
    have hh':(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n)≤
      (((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζglobal*n):=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · intro V U Γ Color _ _ _ _ _ _ G D mm β Q hmm π σ g t J hgood
    apply hRet V U Γ Color G D mm β Q hmm π σ g t J
    exact retained_restriction_good_mono_tolerance π d σ g t _ _ ζ ζglobal J hζglobal hgood
end Oberwolfach
