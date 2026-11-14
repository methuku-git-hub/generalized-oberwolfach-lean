module

public import Oberwolfach.StrongSampledColourCuts

@[expose] public section

/-! A common large-cut event for independently coloured and oriented
physical edges. The cut constants precede the actual colour probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sampledColourOrientation_large_cuts
    (α pstar : ℝ) (hα : 0<α) (hα1 : α≤1/2) (hpstar : 0<pstar)
    (k q₀ : ℕ) :
    ∃ N : ℕ,∀ (V : Type) [Fintype V] [LinearOrder V],N≤Fintype.card V →
    ∀ (P : SimpleGraph V), (∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∀ (ρ : Fin k→ℝ) (hρ : ∀ a,0≤ρ a) (hsum : ∑ a,ρ a=1),
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum)).probability
        (fun σ=>∀ a : Fin k,pstar≤ρ a → ∀ S T : Finset V,
          (1-2*min (α/32) (pstar/512))*Fintype.card V<(S.card:ℝ)+T.card →
          (α*pstar/64)*Fintype.card V*min (S.card:ℝ) T.card≤
            (matrixCut (sampledColourOrientation P σ a) S T:ℝ)) := by
  obtain ⟨N,hN⟩ := sampledColourOrientation_large_cuts_strong α pstar hα hα1 hpstar k q₀
  refine ⟨N,?_⟩
  intro V _ _ hn P hP ρ hρ hsum
  apply (hN V hn P hP ρ hρ hsum).trans
  apply finiteLaw_probability_mono
  intro σ hσ a ha S T hlarge
  have hh := hσ a ha (min (α/32) (pstar/512))
    (min_le_left _ _) ((min_le_right _ _).trans (by linarith only [ha,hpstar])) S T hlarge
  have hc : α*pstar/64≤α*ρ a/4 := by
    have hm := mul_le_mul_of_nonneg_left ha hα.le
    nlinarith only [hm,mul_pos hα hpstar]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (Fintype.card V)))
    (show (0:ℝ)≤min (S.card:ℝ) T.card by positivity)).trans hh

end Oberwolfach
