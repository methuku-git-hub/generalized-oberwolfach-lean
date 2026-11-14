module

public import Oberwolfach.RootedInducedDensity

@[expose] public section

/-! A positive fraction of the fixed-size sets containing prescribed roots
satisfy all induced degree inequalities simultaneously. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fixedSubset_rooted_dense_probability {V : Type*} [Fintype V] [DecidableEq V]
    (T : Finset V) (m : ℕ) (hm : m≤Fintype.card V) (hTm : T.card+1<m)
    [Nonempty (FixedSubset V m)] [Nonempty {S : FixedSubset V m // T⊆S.val}]
    (A : V → Finset V) (δ α : ℝ) (hα : 0<α)
    (hA : ∀ x,(δ+α)*Fintype.card V≤((A x).card:ℝ))
    (hroots : (T.card:ℝ)+1≤α*m/4) :
    1-2*m*Real.exp (-α^2*m/8)≤
      (FiniteLaw.uniform {S : FixedSubset V m // T⊆S.val}).probability
        (fun S=>∀ x∈S.val.val,(δ+α/2)*m<((A x∩S.val.val).card:ℝ)) := by
  let Bad : FixedSubset V m → Prop := fun S=>∃ x∈S.val,((A x∩S.val).card:ℝ)≤(δ+α/2)*m
  have hh := fixedSubset_dense_neighbourhoods T m hm hTm A δ α hα hA hroots
  change (FiniteLaw.uniform (FixedSubset V m)).probability (fun S=>T⊆S.val ∧ Bad S)≤_ at hh
  rw [uniform_probability_intersection (fun S : FixedSubset V m=>T⊆S.val) Bad] at hh
  have hrootpos : 0<(FiniteLaw.uniform (FixedSubset V m)).probability (fun S=>T⊆S.val) := by
    rw [finiteLaw_uniform_probability]
    apply div_pos
    · have hh := Fintype.card_pos (α:={S : FixedSubset V m // T⊆S.val})
      simp only [← Nat.card_eq_fintype_card] at hh ⊢
      exact_mod_cast hh
    · exact_mod_cast Fintype.card_pos (α:=FixedSubset V m)
  have hbad : (FiniteLaw.uniform {S : FixedSubset V m // T⊆S.val}).probability (fun S=>Bad S.val)≤
      2*m*Real.exp (-α^2*m/8) := by
    have hh' :
        (FiniteLaw.uniform (FixedSubset V m)).probability (fun S=>T⊆S.val)*
          (FiniteLaw.uniform {S : FixedSubset V m // T⊆S.val}).probability (fun S=>Bad S.val)≤
        (FiniteLaw.uniform (FixedSubset V m)).probability (fun S=>T⊆S.val)*
          (2*m*Real.exp (-α^2*m/8)) := by
      convert hh using 1 <;> ring
    nlinarith only [hh',hrootpos]
  have hcomp := finiteLaw_probability_compl (FiniteLaw.uniform {S : FixedSubset V m // T⊆S.val}) (fun S=>Bad S.val)
  have he : (fun S : {S : FixedSubset V m // T⊆S.val}=>¬Bad S.val)=
      (fun S=>∀ x∈S.val.val,(δ+α/2)*m<((A x∩S.val.val).card:ℝ)) := by
    funext S
    apply propext
    simp only [Bad,not_exists,not_and,not_le]
  rw [he] at hcomp
  linarith only [hbad,hcomp]


theorem fixedSubset_rooted_dense_card {V : Type*} [Fintype V] [DecidableEq V]
    (T : Finset V) (m : ℕ) (hm : m≤Fintype.card V) (hTm : T.card+1<m)
    (A : V → Finset V) (δ α : ℝ) (hα : 0<α)
    (hA : ∀ x,(δ+α)*Fintype.card V≤((A x).card:ℝ))
    (hroots : (T.card:ℝ)+1≤α*m/4) :
    (1-2*m*Real.exp (-α^2*m/8))*((Fintype.card V-T.card).choose (m-T.card):ℝ)≤
      Fintype.card {S : {S : FixedSubset V m // T⊆S.val} //
        ∀ x∈S.val.val,(δ+α/2)*m<((A x∩S.val.val).card:ℝ)} := by
  letI : Nonempty (FixedSubset V m) := fixedSubset_nonempty hm
  letI : Nonempty {S : FixedSubset V m // T⊆S.val} :=
    fixedSubset_containing_nonempty T m (by omega) hm
  have hh := fixedSubset_rooted_dense_probability T m hm hTm A δ α hα hA hroots
  rw [finiteLaw_uniform_probability] at hh
  have hpos : (0:ℝ)<Fintype.card {S : FixedSubset V m // T⊆S.val} := by
    exact_mod_cast Fintype.card_pos (α:={S : FixedSubset V m // T⊆S.val})
  have hc : (Fintype.card {S : FixedSubset V m // T⊆S.val}:ℝ)=
      ((Fintype.card V-T.card).choose (m-T.card):ℝ) := by
    have hh := fixedSubset_containing_card (r:=m) T (by omega)
    simp only [← Nat.card_eq_fintype_card] at hh ⊢
    exact_mod_cast hh
  have hh' := (le_div_iff₀ hpos).mp hh
  rw [hc] at hh'
  convert hh' using 1 <;> congr!

end Oberwolfach
