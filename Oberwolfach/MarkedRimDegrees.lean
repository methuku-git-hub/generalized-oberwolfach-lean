module

public import Oberwolfach.PermutationMatrixDegrees
public import Oberwolfach.MarkedPhysicalCuts
public import Oberwolfach.ColourDegreeEvent

@[expose] public section

/-! Directed degrees of the actual marked rims. The incoming marked
centre is the parent degree at the physical successor of the root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [LinearOrder V]

theorem markedPhysicalRim_degree_event
    (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (t : ℝ) (ht : 0≤t) :
    1-18*Fintype.card V*Real.exp (-2*t^2/Fintype.card V)≤
    (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
      (fun σ=>∀ a x,
        |((∑ y,markedPhysicalRim P π b σ a x y:ℕ):ℝ)-(if a then k else p)*P.degree x|≤t+(2*b+1) ∧
        |((∑ y,markedPhysicalRim P π b σ a y x:ℕ):ℝ)-(if a then k else p)*P.degree (if a then π x else x)|≤t+(2*b+1)) := by
  let E := fun M : Bool→V→V→ℕ=>∀ a x,
    |((∑ y,permutationSeparatedMatrix π b (M a) x y:ℕ):ℝ)-(if a then k else p)*P.degree x|≤t+(2*b+1) ∧
    |((∑ y,permutationSeparatedMatrix π b (M a) y x:ℕ):ℝ)-(if a then k else p)*P.degree (if a then π x else x)|≤t+(2*b+1)
  change 1-18*Fintype.card V*Real.exp (-2*t^2/Fintype.card V)≤
    (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
      (fun σ=>E (markedPhysicalOrientation P π σ))
  rw [markedPhysical_orientation_probability P π p k hp hk hsum E]
  have hh := sampledColourDegrees_common_event P P (markedPhysicalProbability p k)
    (markedPhysicalProbability_nonneg p k hp hk hsum) (markedPhysicalProbability_sum p k) ht
  have hh' : 1-18*Fintype.card V*Real.exp (-2*t^2/Fintype.card V)≤
    (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.categoricalDirection (markedPhysicalProbability p k)
      (markedPhysicalProbability_nonneg p k hp hk hsum) (markedPhysicalProbability_sum p k))).probability
      (fun σ=>∀ a x,
        |((∑ y,sampledColourOrientation P σ a x y:ℕ):ℝ)-markedPhysicalProbability p k a/2*P.degree x|<t ∧
        |((∑ y,sampledColourOrientation P σ a y x:ℕ):ℝ)-markedPhysicalProbability p k a/2*P.degree x|<t ∧
        |(sampledColourDegree P (fun e=>(σ e).1) a x:ℝ)-markedPhysicalProbability p k a*P.degree x|<t) := by
    convert hh using 1 <;> norm_num
  apply hh'.trans
  apply finiteLaw_probability_mono
  intro σ hσ a x
  let M := fun x y=>sampledColourOrientation P σ (if a then 1 else 0) x (if a then π y else y)
  have hM (x y : V) : M x y≤1 := by dsimp [M,sampledColourOrientation];split_ifs <;> omega
  have hout : |((∑ y,M x y:ℕ):ℝ)-(if a then k else p)*P.degree x|<t := by
    cases a
    · simpa [M,markedPhysicalProbability] using (hσ 0 x).1
    · have he : (∑ y,sampledColourOrientation P σ 1 x (π y))=∑ y,sampledColourOrientation P σ 1 x y :=
        Equiv.sum_comp π (fun y=>sampledColourOrientation P σ 1 x y)
      simpa [M,he,markedPhysicalProbability] using (hσ 1 x).1
  have hin : |((∑ y,M y x:ℕ):ℝ)-(if a then k else p)*P.degree (if a then π x else x)|<t := by
    cases a
    · simpa [M,markedPhysicalProbability] using (hσ 0 x).2.1
    · simpa [M,markedPhysicalProbability] using (hσ 1 (π x)).2.1
  have hrow := permutationSeparatedMatrix_row_loss π b M hM x
  have hcol := permutationSeparatedMatrix_column_loss π b M hM x
  change |((∑ y,permutationSeparatedMatrix π b M x y:ℕ):ℝ)-(if a then k else p)*P.degree x|≤_ ∧
    |((∑ y,permutationSeparatedMatrix π b M y x:ℕ):ℝ)-(if a then k else p)*P.degree (if a then π x else x)|≤_
  constructor
  · exact (abs_sub_le _ ((∑ y,M x y:ℕ):ℝ) _).trans (by linarith only [hrow,hout])
  · exact (abs_sub_le _ ((∑ y,M y x:ℕ):ℝ) _).trans (by linarith only [hcol,hin])

end Oberwolfach
