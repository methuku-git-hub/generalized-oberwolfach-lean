module

public import Mathlib.Tactic

@[expose] public section

/-! Explicit intervals avoiding at most one exceptional interface. -/
set_option autoImplicit false
namespace Oberwolfach

def HasCleanBlock (J : Finset ℕ) (a L t : ℕ) : Prop :=
  ∃ s : ℕ, a ≤ s ∧ s+t ≤ a+L ∧ ∀ j, s ≤ j → j < s+t → j ∉ J

theorem two_blocks_one_exception (J : Finset ℕ) (hJ : J.card ≤ 1)
    (a L t : ℕ) (hL : 2*t ≤ L) : HasCleanBlock J a L t := by
  classical
  by_cases hfirst : ∀ j, a ≤ j → j < a+t → j ∉ J
  · exact ⟨a,le_rfl,by omega,hfirst⟩
  push Not at hfirst
  obtain ⟨e,hae,het,heJ⟩ := hfirst
  refine ⟨a+t,by omega,by omega,?_⟩
  intro j hj hjt hjJ
  have heq : e=j := (Finset.card_le_one.mp hJ) e heJ j hjJ
  omega

theorem edge_has_clean_prefix_or_suffix (J : Finset ℕ) (hJ : J.card ≤ 1)
    (a L t e : ℕ) (hL : 4*t+1 ≤ L) (he : a ≤ e) (heL : e < a+L) :
    HasCleanBlock J a (e-a) t ∨ HasCleanBlock J (e+1) (a+L-(e+1)) t := by
  by_cases hpre : 2*t ≤ e-a
  · exact Or.inl (two_blocks_one_exception J hJ a (e-a) t hpre)
  · exact Or.inr (two_blocks_one_exception J hJ (e+1) (a+L-(e+1)) t (by omega))

theorem three_long_intervals (c t : ℕ) (hc : 12*t+4 ≤ c) :
    ∃ L : Fin 3 → ℕ, (∀ i, 4*t+1 ≤ L i) ∧ (∑ i, L i)=c := by
  refine ⟨![4*t+1,4*t+1,c-(8*t+2)],?_,?_⟩
  · intro i
    fin_cases i <;> simp <;> omega
  · simp [Fin.sum_univ_succ]
    omega

end Oberwolfach
