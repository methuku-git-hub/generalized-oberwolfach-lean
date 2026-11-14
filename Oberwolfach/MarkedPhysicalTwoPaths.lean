module

public import Oberwolfach.PermutationTwoStepCounts
public import Oberwolfach.ColourOrientationTwoPathEvent
public import Oberwolfach.MarkedPhysicalCuts

@[expose] public section

/-! The ordinary two-step paths in the original five-state marked experiment.
The two roots need only be distinct, and the realised separation loss has
no density factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [LinearOrder V]

theorem markedPhysicalRim_twoPaths_event
    (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (t : ℝ) (ht : 0≤t) :
    1-2*(Fintype.card V:ℝ)^2*Real.exp (-t^2/Fintype.card V)≤
    (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
      (fun σ=>∀ x y,x≠y →
        ((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-t-2*(2*(b:ℝ)+1)≤
        ((Finset.univ.filter (fun z=>0<markedPhysicalRim P π b σ false x z ∧
          0<markedPhysicalRim P π b σ false z y)).card:ℝ)) := by
  let E := fun M : Bool→V→V→ℕ=>∀ x y,x≠y →
    ((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-t-2*(2*(b:ℝ)+1)≤
      ((Finset.univ.filter (fun z=>0<permutationSeparatedMatrix π b (M false) x z ∧
        0<permutationSeparatedMatrix π b (M false) z y)).card:ℝ)
  change 1-2*(Fintype.card V:ℝ)^2*Real.exp (-t^2/Fintype.card V)≤
    (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
      (fun σ=>E (markedPhysicalOrientation P π σ))
  rw [markedPhysical_orientation_probability P π p k hp hk hsum E]
  have hh := sampledColourOrientation_twoPaths_common_event P P le_rfl
    (markedPhysicalProbability p k) (markedPhysicalProbability_nonneg p k hp hk hsum)
    (markedPhysicalProbability_sum p k) 0 ht
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ x y hxy
  let M := sampledColourOrientation P σ (0:Fin 3)
  have hMP : ∀ x y,0<M x y → P.Adj x y := by
    intro x y h
    dsimp [M,sampledColourOrientation] at h
    split_ifs at h with hc
    · exact hc.1
    · omega
  have hcount := hσ x y hxy
  simp only [markedPhysicalProbability,Matrix.cons_val_zero,show 2*p/2=p by ring] at hcount
  have he := eligibleTwoPathCount_eq_univ P M hMP x y
  have hcount' : |((Finset.univ.filter (fun z=>0<M x z ∧ 0<M z y)).card:ℝ)-
      ((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2|<t := by
    simpa only [M,← he] using hcount
  have hloss := permutationSeparatedMatrix_two_step_loss π b M x y
  have hlo := (abs_lt.mp hcount').1
  have hlosshi := neg_le_abs
    (((Finset.univ.filter (fun z=>0<permutationSeparatedMatrix π b M x z ∧
       0<permutationSeparatedMatrix π b M z y)).card:ℝ)-
      (Finset.univ.filter (fun z=>0<M x z ∧ 0<M z y)).card)
  have hresult : ((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-t-2*(2*(b:ℝ)+1)≤
      ((Finset.univ.filter (fun z=>0<permutationSeparatedMatrix π b M x z ∧
        0<permutationSeparatedMatrix π b M z y)).card:ℝ) := by
    linarith only [hlo,hloss,hlosshi]
  convert hresult using 1 <;> congr!

end Oberwolfach
