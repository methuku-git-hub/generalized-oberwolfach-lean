module

public import Oberwolfach.MarkedIterationErrorScales

@[expose] public section

/-! Explicit choices of the two uniform deletion allowances. The global
allowance precedes the later analytic tolerance x; the star allowance is
chosen after x and before the inner balance and order thresholds. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Oberwolfach

theorem marked_iteration_global_tolerance_choice
    (r h : ℕ) (κ γ p k omega C θ b : ℝ)
    (hκ : 0<κ) (hγ : 0<γ) (hp : 0<p) (hk : 0<k) (ho : 0<omega)
    (hC : 0≤C) (hθ : 0<θ) (hb : 0<b) :
    ∃ ζmax : ℝ,0<ζmax ∧ ∀ ε ζ : ℝ,ε≤κ/4→0≤ζ→ζ≤ζmax→
      ε+ζ≤κ ∧ ε+4*ζ≤κ ∧ ε+2*h*ζ≤κ ∧ ε+h*ζ≤κ ∧
      ζ≤(κ-ε)*omega ∧ ε≤κ ∧ 2*ζ≤(3/4)*γ*p^2 ∧ ζ≤γ*min p k/8 ∧
      C*ζ≤κ/4 ∧ C*ζ≤θ/4 ∧ 2*(r+5:ℝ)*ζ≤b ∧ (2*r+11:ℝ)*ζ≤b := by
  obtain ⟨z0,hz0,hbase⟩ := marked_iteration_reference_scale h κ γ p k omega C hκ hγ hp hk ho hC
  let zmax := min z0 (min (θ/(4*(C+1))) (b/(2*(r:ℝ)+12)))
  refine ⟨zmax,by dsimp [zmax];positivity,?_⟩
  intro ε ζ he hz hzmax
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := hbase ε ζ he hz (hzmax.trans (min_le_left _ _))
  have ht := (hzmax.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hb' := (hzmax.trans (min_le_right _ _)).trans (min_le_right _ _)
  have ht' := (le_div_iff₀ (show 0<4*(C+1) by positivity)).mp ht
  have hb'' := (le_div_iff₀ (show 0<2*(r:ℝ)+12 by positivity)).mp hb'
  refine ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,?_,?_,?_⟩
  · nlinarith only [ht',hz]
  · nlinarith only [hb'',hz]
  · nlinarith only [hb'',hz]

theorem marked_iteration_local_tolerance_choice
    (m h : ℕ) (x eps C t β η : ℝ)
    (hx : 0<x) (heps : 0<eps) (hC : 0≤C) (ht : 0<t) (hβ : 0<β) (hη : 0<η) :
    ∃ sigmaMax : ℝ,0<sigmaMax ∧ ∀ sigma : ℝ,0≤sigma→sigma≤sigmaMax→
      (m+2:ℝ)*sigma≤x/4 ∧ 2*(h:ℝ)*sigma≤x/2 ∧
      4*C*sigma/eps≤min (t/8) (min β (η/4)) := by
  let b := min (t/8) (min β (η/4))
  have hb : 0<b := by dsimp [b];positivity
  let sigmaMax := min (x/(4*((m:ℝ)+2)))
    (min (x/(4*((h:ℝ)+1))) (eps*b/(4*(C+1))))
  refine ⟨sigmaMax,by dsimp [sigmaMax];positivity,?_⟩
  intro sigma hs hmax
  have h1 := hmax.trans (min_le_left _ _)
  have h2 := (hmax.trans (min_le_right _ _)).trans (min_le_left _ _)
  have h3 := (hmax.trans (min_le_right _ _)).trans (min_le_right _ _)
  have h1' := (le_div_iff₀ (show 0<4*((m:ℝ)+2) by positivity)).mp h1
  have h2' := (le_div_iff₀ (show 0<4*((h:ℝ)+1) by positivity)).mp h2
  have h3' := (le_div_iff₀ (show 0<4*(C+1) by positivity)).mp h3
  refine ⟨by nlinarith only [h1'],by nlinarith only [h2',hs],?_⟩
  apply (div_le_iff₀ heps).mpr
  change 4*C*sigma≤b*eps
  nlinarith only [h3',hs]

end Oberwolfach
