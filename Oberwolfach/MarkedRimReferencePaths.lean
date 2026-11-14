module

public import Oberwolfach.MarkedPhysicalTwoPaths

@[expose] public section

/-! The source lower bound for ordinary directed two-step paths, uniformly
in the actual retained density above its fixed positive lower bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [LinearOrder V]

theorem markedPhysicalRim_reference_paths
    (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (γ pstar : ℝ) (hγ : 0≤γ) (hpstar : 0≤pstar) (hlo : pstar≤p)
    (hP : ∀ x,(1/2+γ)*Fintype.card V≤(P.degree x:ℝ))
    (hmask : 2*(2*(b:ℝ)+1)≤γ*pstar^2*Fintype.card V/4) :
    1-2*(Fintype.card V:ℝ)^2*Real.exp (-(γ*pstar^2*Fintype.card V/4)^2/Fintype.card V)≤
    (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
      (fun σ=>∀ x y,x≠y →
        3/2*γ*p^2*Fintype.card V≤
        ((Finset.univ.filter (fun z=>0<markedPhysicalRim P π b σ false x z ∧
          0<markedPhysicalRim P π b σ false z y)).card:ℝ)) := by
  have hh := markedPhysicalRim_twoPaths_event P π b p k hp hk hsum
    (γ*pstar^2*Fintype.card V/4) (by positivity)
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ x y hxy
  have hc := commonNeighbours_lower_of_minDegree P γ hP x y
  have hmul := mul_le_mul_of_nonneg_right hc (sq_nonneg p)
  have hp2 : pstar^2≤p^2 := by nlinarith only [hpstar,hlo]
  have htp := mul_le_mul_of_nonneg_left hp2 (show 0≤γ*(Fintype.card V:ℝ) by positivity)
  linarith only [hσ x y hxy,hmul,htp,hmask]

end Oberwolfach
