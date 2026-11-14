module

public import Oberwolfach.MarkedRimDegrees

@[expose] public section

/-! Recentring both marked rim degrees at the fixed reference degree.
The degree at pi(x) is used before invoking the parent regularity bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [LinearOrder V]

theorem markedPhysicalRim_reference_degrees
    (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (D ε δP : ℝ) (hε : 0≤ε) (hδ : 0≤δP) (hδε : δP≤ε/4)
    (hP : ∀ x,|(P.degree x:ℝ)-D|≤δP*Fintype.card V)
    (hmask : 2*(b:ℝ)+1≤ε*Fintype.card V/4) :
    1-18*Fintype.card V*Real.exp (-2*(ε*Fintype.card V/2)^2/Fintype.card V)≤
    (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
      (fun σ=>∀ a x,
        |((∑ y,markedPhysicalRim P π b σ a x y:ℕ):ℝ)-(if a then k else p)*D|≤ε*Fintype.card V ∧
        |((∑ y,markedPhysicalRim P π b σ a y x:ℕ):ℝ)-(if a then k else p)*D|≤ε*Fintype.card V) := by
  have hh := markedPhysicalRim_degree_event P π b p k hp hk hsum (ε*Fintype.card V/2) (by positivity)
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ a x
  have ha : 0≤(if a then k else p) := by cases a <;> assumption
  have ha1 : (if a then k else p)≤1 := by cases a <;> simp only [Bool.false_eq_true,↓reduceIte] <;> linarith
  have hcenter (v : V) : |(if a then k else p)*(P.degree v:ℝ)-(if a then k else p)*D|≤ε*Fintype.card V/4 := by
    rw [← mul_sub,abs_mul,abs_of_nonneg ha]
    calc
      _ ≤ (if a then k else p)*(δP*Fintype.card V) := mul_le_mul_of_nonneg_left (hP v) ha
      _ ≤ δP*Fintype.card V := by nlinarith only [ha1,show 0≤δP*(Fintype.card V:ℝ) by positivity]
      _ ≤ ε*Fintype.card V/4 := by nlinarith only [mul_le_mul_of_nonneg_right hδε (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))]
  constructor
  · have htri := abs_sub_le ((∑ y,markedPhysicalRim P π b σ a x y:ℕ):ℝ)
      ((if a then k else p)*P.degree x) ((if a then k else p)*D)
    linarith only [htri,(hσ a x).1,hcenter x,hmask]
  · have htri := abs_sub_le ((∑ y,markedPhysicalRim P π b σ a y x:ℕ):ℝ)
      ((if a then k else p)*P.degree (if a then π x else x)) ((if a then k else p)*D)
    linarith only [htri,(hσ a x).2,hcenter (if a then π x else x),hmask]

end Oberwolfach
