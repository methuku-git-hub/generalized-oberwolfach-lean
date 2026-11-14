module

public import Oberwolfach.OrdinaryTriangleReferenceProbability
public import Oberwolfach.OrdinaryInducedRimCutProbability
public import Oberwolfach.OrdinaryInducedRimThresholdHalfDensity

@[expose] public section
/-! The ambient reference cuts and the induced rim cut hold together on the
    original sample with the same physical direction coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reference_and_inner_rim_high_probability
    (α αinner pstar ω : ℝ) (hα : 0<α) (hα1 : α≤1/2)
    (hαinner : 0<αinner) (hαinner1 : αinner≤1/2)
    (hpstar : 0<pstar) (hpstar1 : pstar≤1) (hω : 0<ω) :
    ∃ δ h : ℝ, 0<δ ∧ δ<1/4 ∧ 0<h ∧
    ∀ L : ℝ,0≤L → ∀ d q₀ : ℕ,∀ hd : 2≤d,∃ N : ℕ,
    ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (P F : SimpleGraph V) (I : Finset V), N≤I.card →
      (∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ)) →
      (∀ v,(F.degree v:ℝ)≤L) →
    ∀ density : ℝ, (1/2:ℝ)+αinner≤density →
      (∀ v∈I,density*I.card≤((I∩P.neighborFinset v).card:ℝ)) →
    ∀ (π : Equiv.Perm V),(∀ x k,0<k → k<2*d+1 → (π^k) x≠x) →
    ∀ (pR pH : ℝ) (hR : 0≤pR) (hR1 : pR≤1),pstar≤pR → pstar≤pH →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Color),(∀ u,s u j=pH) →
    let μ := (FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>hR) (fun _=>hR1)
      d hd q hq hQ s hs hS)).prod (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.fairCoin))
    1-1/(Fintype.card V:ℝ)^q₀-1/(I.card:ℝ)^q₀≤μ.probability (fun z=>
      OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2 ∧
      OrdinaryInducedRimCutEvent I (sampledOrientation (rawWheelGraph P z.1) z.2) αinner pstar) := by
  obtain ⟨δ,h,hδ,hδsmall,hh,hmain⟩:=ordinary_triangle_reference_matrix_high_probability α pstar ω hα hα1 hpstar hpstar1 hω
  refine ⟨δ,h,hδ,hδsmall,hh,?_⟩
  intro L hL d q₀ hd
  obtain ⟨N₁,hN₁⟩:=hmain L hL d q₀ hd
  obtain ⟨N₂,hN₂⟩:=ordinary_induced_rim_cut_high_probability αinner pstar hαinner hαinner1 hpstar q₀
  refine ⟨max N₁ N₂,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hlo hhi P F I hI hP hF density hdensity hmin π hnoshort pR pH hR hR1 hpR hpH q hq hQ s hs hS j hj μ
  have hdegree:=ordinary_induced_rim_threshold_from_half_density P I density αinner hdensity hmin
  have href:=hN₁ V U Γ Color (le_trans (le_max_left _ _) hn) hlo hhi P F hP hF π hnoshort
    pR pH hR hR1 hpR hpH q hq hQ s hs hS j hj
  have hrim:=hN₂ V U Γ Color P I (le_trans (le_max_right _ _) hI) hdegree pR hR hR1 hpR d hd q hq hQ s hs hS
  let A:=fun z:RawWheelOutcome V U Γ Color×(Sym2 V→Bool)=>
    OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2
  let B:=fun z:RawWheelOutcome V U Γ Color×(Sym2 V→Bool)=>
    OrdinaryInducedRimCutEvent I (sampledOrientation (rawWheelGraph P z.1) z.2) αinner pstar
  have hA:1-1/(Fintype.card V:ℝ)^q₀≤μ.probability A:=by
    convert href using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hB:1-1/(I.card:ℝ)^q₀≤μ.probability B:=by
    convert hrim using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  exact (sub_le_sub_right hA (1/(I.card:ℝ)^q₀)).trans (finiteLaw_good_intersection μ A B _ hB)
end Oberwolfach
