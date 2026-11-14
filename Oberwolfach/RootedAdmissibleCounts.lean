module

public import Oberwolfach.RootedAdmissibleDensity
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-! Actual counts of dense, conflict-free sets containing the prescribed roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rootedSubset_dense_conflict_free_card {V : Type*} [Fintype V] [DecidableEq V]
    (P F : SimpleGraph V) (T : Finset V) (k : ℕ) (hk : T.card+k≤Fintype.card V) (hk2 : 2≤k)
    (δ α L : ℝ) (hα : 0<α)
    (hP : ∀ v,(δ+α)*Fintype.card V≤(P.degree v:ℝ))
    (hF : ∀ v,(F.degree v:ℝ)≤L)
    (hT : ∀ x∈T,∀ y∈T,¬F.Adj x y)
    (hroots : (T.card:ℝ)+1≤α*(T.card+k:ℝ)/4) :
    let q : ℝ := (k:ℝ)/(Fintype.card V-T.card:ℕ)
    (1-2*(T.card+k:ℝ)*Real.exp (-α^2*(T.card+k:ℝ)/8)-
        L*(2*(T.card:ℝ)*q+Fintype.card V*q^2))*
        ((Fintype.card V-T.card).choose k:ℝ)≤
      Fintype.card {S : RootedSubset V T k //
        (∀ v∈S.val.val,(δ+α/2)*(T.card+k:ℝ)<((P.neighborFinset v∩S.val.val).card:ℝ)) ∧
        (∀ x∈S.val.val,∀ y∈S.val.val,¬F.Adj x y)} := by
  intro q
  let : Nonempty (RootedSubset V T k) := rootedSubset_nonempty T k hk
  have hh := rootedSubset_dense_conflict_free_probability P F T k hk hk2 δ α L hα hP hF hT hroots
  rw [finiteLaw_uniform_probability] at hh
  have hpos : (0:ℝ)<Fintype.card (RootedSubset V T k) := by
    exact_mod_cast Fintype.card_pos (α:=RootedSubset V T k)
  have hc : (Fintype.card (RootedSubset V T k):ℝ)=((Fintype.card V-T.card).choose k:ℝ) := by
    have hh := fixedSubset_containing_card (r:=T.card+k) T (by omega)
    simp only [Nat.add_sub_cancel_left,← Nat.card_eq_fintype_card] at hh ⊢
    exact_mod_cast hh
  have hh' := (le_div_iff₀ hpos).mp hh
  rw [hc] at hh'
  convert hh' using 1 <;> congr!


theorem choose_rooted_power_lower (n s k : ℕ) (h : 2*(s+k)≤n) :
    (n:ℝ)^k/((2:ℝ)^k*k.factorial)≤((n-s).choose k:ℝ) := by
  have hns : s≤n := by omega
  have hkn : k≤n-s+1 := by omega
  have hbase : (n:ℝ)/2≤(n-s+1-k:ℕ) := by
    rw [Nat.cast_sub hkn,Nat.cast_add,Nat.cast_one,Nat.cast_sub hns]
    have hh : (2:ℝ)*(s+k)≤n := by exact_mod_cast h
    linarith
  calc
    _ = ((n:ℝ)/2)^k/k.factorial := by rw [div_pow,div_div]
    _ ≤ ((n-s+1-k:ℕ):ℝ)^k/k.factorial :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase k) (by positivity)
    _ ≤ _ := Nat.pow_le_choose k (n-s)

end Oberwolfach
