module

public import Oberwolfach.OrdinaryReferenceCuts
public import Oberwolfach.OrdinaryTriangleReferenceJoint

@[expose] public section
/-! The matrix reference event used by the matching and cover bundle has
    high probability for the original ambient wheel law and direction coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_reference_matrix_high_probability
    (α pstar ω : ℝ) (hα : 0<α) (hα1 : α≤1/2)
    (hpstar : 0<pstar) (hpstar1 : pstar≤1) (hω : 0<ω) :
    ∃ δ h : ℝ, 0<δ ∧ δ<1/4 ∧ 0<h ∧
    ∀ L : ℝ,0≤L → ∀ d q₀ : ℕ,∀ hd : 2≤d,∃ N : ℕ,
    ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ P F : SimpleGraph V,(∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ)) →
      (∀ v,(F.degree v:ℝ)≤L) →
    ∀ (π : Equiv.Perm V),(∀ x k,0<k → k<2*d+1 → (π^k) x≠x) →
    ∀ (pR pH : ℝ) (hR : 0≤pR) (hR1 : pR≤1),pstar≤pR → pstar≤pH →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Color),(∀ u,s u j=pH) →
    let μ := (FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>hR) (fun _=>hR1)
      d hd q hq hQ s hs hS)).prod (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.fairCoin))
    1-1/(Fintype.card V:ℝ)^q₀≤μ.probability (fun z=>
      OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2) := by
  obtain ⟨δ,h,hδ,hδsmall,hh,hmain⟩:=ordinary_reference_large_cuts α pstar ω hα hα1 hpstar hpstar1 hω
  refine ⟨δ,h,hδ,hδsmall,hh,?_⟩
  intro L hL d q₀ hd
  obtain ⟨N,hN⟩:=hmain L hL d q₀ hd
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hlo hhi P F hP hF π hnoshort pR pH hR hR1 hpR hpH q hq hQ s hs hS j hj μ
  have hb:=hN V U Γ Color hn hlo hhi P F hP hF π hnoshort pR pH hR hR1 hpR hpH q hq hQ s hs hS j hj
  exact hb
end Oberwolfach
