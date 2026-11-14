module

public import Oberwolfach.StrongSampledColourCuts
public import Oberwolfach.PermutationMatrixCuts

@[expose] public section

/-! One physical-colour event controls all permuted column cuts, after
removing the actual short-distance auxiliary arcs. The deletion is a
realised loss of at most 2b+1 per row and per column, without a density
factor. Constants are uniform over the actual colour probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sampledColourOrientation_separated_large_cuts
    (α pstar : ℝ) (hα : 0<α) (hα1 : α≤1/2) (hpstar : 0<pstar)
    (k b q₀ : ℕ) :
    ∃ N : ℕ,∀ (V : Type) [Fintype V] [LinearOrder V],N≤Fintype.card V →
    ∀ (P : SimpleGraph V), (∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∀ (ρ : Fin k→ℝ) (hρ : ∀ a,0≤ρ a) (hsum : ∑ a,ρ a=1),
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum)).probability
        (fun σ=>∀ a : Fin k,pstar≤ρ a → ∀ (π τ : Equiv.Perm V),
          ∀ δ : ℝ,δ≤α/32 → δ≤ρ a/64 → ∀ S T : Finset V,
          (1-2*δ)*Fintype.card V<(S.card:ℝ)+T.card →
          (α*ρ a/8)*Fintype.card V*min (S.card:ℝ) T.card≤
            (matrixCut (permutationSeparatedMatrix π b
              (fun x y=>sampledColourOrientation P σ a x (τ y))) S T:ℝ)) := by
  obtain ⟨N,hN⟩ := sampledColourOrientation_large_cuts_strong α pstar hα hα1 hpstar k q₀
  obtain ⟨K,hK⟩ := exists_nat_ge ((2*(b:ℝ)+1)*8/(α*pstar))
  refine ⟨max N K,?_⟩
  intro V _ _ hn P hP ρ hρ hsum
  apply (hN V (le_trans (le_max_left _ _) hn) P hP ρ hρ hsum).trans
  apply finiteLaw_probability_mono
  intro σ hσ a ha π τ δ hδα hδρ S T hlarge
  have hcard : (T.image τ).card=T.card := Finset.card_image_iff.mpr (fun x _ y _ h=>τ.injective h)
  have hcut := hσ a ha δ hδα hδρ S (T.image τ) (by simpa only [hcard] using hlarge)
  rw [hcard,← matrixCut_permute_columns] at hcut
  have hloss := permutationSeparatedMatrix_cut_loss π b
    (fun x y=>sampledColourOrientation P σ a x (τ y))
    (by intro x y;unfold sampledColourOrientation;split_ifs <;> omega) S T
  have hKn : (K:ℝ)≤Fintype.card V := by exact_mod_cast (le_trans (le_max_right N K) hn)
  have hmargin : 2*(b:ℝ)+1≤α*pstar/8*Fintype.card V := by
    have hh := (div_le_iff₀ (mul_pos hα hpstar)).mp (hK.trans hKn)
    nlinarith only [hh]
  have hscale := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ha hα.le) (Nat.cast_nonneg (Fintype.card V))
  have hmargin' : 2*(b:ℝ)+1≤α*ρ a/8*Fintype.card V := by nlinarith only [hmargin,hscale]
  have hm := mul_le_mul_of_nonneg_right hmargin'
    (show (0:ℝ)≤min (S.card:ℝ) T.card by positivity)
  nlinarith only [hcut,hloss,hm]

end Oberwolfach
