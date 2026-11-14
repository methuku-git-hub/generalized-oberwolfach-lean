module

public import Oberwolfach.RawIntervalSpokeCuts
public import Oberwolfach.OrdinaryRawIntervalSampling

@[expose] public section

/-! The ordinary spoke-cut event as an event of the original joint
physical-edge and interval experiment. Physical retention probabilities are
unchanged and may be nonconstant. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rawWheelSpokeCuts_uniform_probability
    (pstar ω : ℝ) (hpstar : 0<pstar) (hpstar1 : pstar≤1) (hω : 0<ω)
    (d q₀ : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (π : Equiv.Perm V) (ρ : Sym2 V → ℝ) (hρ : ∀ e,0≤ρ e) (hρ1 : ∀ e,ρ e≤1)
      (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Color),(∀ x k,0<k → k<2*d+1 → (π^k) x≠x) →
    ∀ pH : ℝ,pstar≤pH → (∀ u,s u j=pH) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ (X : Finset V) (Y : Finset U),
          1-pstar/8<(X.card:ℝ)/Fintype.card V+(Y.card:ℝ)/Fintype.card U →
          pstar/8*min ((Fintype.card U:ℝ)*X.card) ((Fintype.card V:ℝ)*Y.card)≤
            (bipartiteMatrixCut (fun v u=>if rawWheelSpokes π d σ j v u then 1 else 0) X Y:ℝ)) := by
  obtain ⟨N,hN⟩ := rawIntervalSpokeMatrix_large_cuts pstar ω hpstar hpstar1 hω d q₀ hd
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hmlo hmhi π ρ hρ hρ1 q hq hQ s hs hS j hnoshort pH hpH hj
  have hh := hN V U Γ Color hn hmlo hmhi π q hq hQ s hs hS j hnoshort pH hpH hj
  have hp := finiteLaw_pi_injective_projection_event
    (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS) Sum.inr Sum.inr_injective
    (fun σ=>∀ (X : Finset V) (Y : Finset U),
      1-pstar/8<(X.card:ℝ)/Fintype.card V+(Y.card:ℝ)/Fintype.card U →
      pstar/8*min ((Fintype.card U:ℝ)*X.card) ((Fintype.card V:ℝ)*Y.card)≤
        (bipartiteMatrixCut (rawIntervalSpokeMatrix π d σ j) X Y:ℝ))
  erw [← hp] at hh
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ X Y hXY
  have h := hσ X Y hXY
  convert h using 1
  congr 2
  funext v u
  unfold rawIntervalSpokeMatrix rawWheelSpokes
  split_ifs <;> rfl

end Oberwolfach
