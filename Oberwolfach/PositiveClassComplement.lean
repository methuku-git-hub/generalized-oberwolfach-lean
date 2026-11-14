module

public import Mathlib.Tactic

@[expose] public section
/-! Among nonempty classes with a common density lower bound, either the
chosen class is the only one or its complement has the same lower bound. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem positive_class_complement_dichotomy
    {I:Type} [Fintype I] [DecidableEq I] (ρ:I→ℝ) (r:ℝ)
    (hnonneg:∀i,0≤ρ i) (htotal:∑i,ρ i=1) (hlow:∀i,r≤ρ i) (a:I):
    ρ a=1 ∨ r≤1-ρ a:=by
  classical
  by_cases h:∃b:I,b≠a
  · right
    obtain ⟨b,hba⟩:=h
    have hmem:b∈(Finset.univ:Finset I).erase a:=by simp [hba]
    have hb:ρ b≤∑i∈(Finset.univ:Finset I).erase a,ρ i:=
      Finset.single_le_sum (fun i _=>hnonneg i) hmem
    have hs:=Finset.sum_erase_add Finset.univ ρ (Finset.mem_univ a)
    rw [htotal] at hs
    linarith [hlow b]
  · left
    have hsing:(Finset.univ:Finset I)={a}:=by
      ext i
      simp only [Finset.mem_univ,Finset.mem_singleton,true_iff]
      by_contra hia
      exact h ⟨i,hia⟩
    rw [hsing] at htotal
    simpa using htotal
end Oberwolfach

namespace Oberwolfach

theorem positive_class_binary_group_dichotomy
    {I:Type} [Fintype I] [DecidableEq I] (ρ:I→ℝ) (r:ℝ)
    (hnonneg:∀i,0≤ρ i) (htotal:∑i,ρ i=1) (hlow:∀i,r≤ρ i) (a:I):
    ρ a=1 ∨ ∀i:Fin 2,r≤(![ρ a,1-ρ a] : Fin 2→ℝ) i:=by
  rcases positive_class_complement_dichotomy ρ r hnonneg htotal hlow a with hone|hcomp
  · exact Or.inl hone
  · right
    intro i
    fin_cases i <;> simp [hlow a,hcomp]
end Oberwolfach
