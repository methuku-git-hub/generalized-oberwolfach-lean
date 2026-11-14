module

public import Oberwolfach.RootedAdmissibleCounts
public import Oberwolfach.RootedDenseSetScales

@[expose] public section

/-! A polynomial lower bound for dense conflict-free bounded sets. The
bounded size is chosen before the maximum conflict degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rootedSubset_dense_conflict_free_many (s : ℕ) (α : ℝ) (hα : 0<α) :
    ∃ K : ℕ,∀ k : ℕ,K≤k → ∀ L : ℝ,0≤L → ∃ N : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
    ∀ (P F : SimpleGraph V) (T : Finset V),T.card=s → ∀ δ : ℝ,
    (∀ v,(δ+α)*Fintype.card V≤(P.degree v:ℝ)) →
    (∀ v,(F.degree v:ℝ)≤L) → (∀ x∈T,∀ y∈T,¬F.Adj x y) →
    (Fintype.card V:ℝ)^k/((2:ℝ)^(k+1)*k.factorial)≤
      Fintype.card {S : RootedSubset V T k //
        (∀ v∈S.val.val,(δ+α/2)*(s+k:ℝ)<((P.neighborFinset v∩S.val.val).card:ℝ)) ∧
        (∀ x∈S.val.val,∀ y∈S.val.val,¬F.Adj x y)} := by
  obtain ⟨K,hK⟩ := rooted_dense_set_scales s α hα
  refine ⟨K,?_⟩
  intro k hk L hL
  obtain ⟨hk2,hroots,hfailure,hN⟩ := hK k hk
  obtain ⟨N,hN⟩ := hN L hL
  refine ⟨N,?_⟩
  intro V _ _ hn P F T hT δ hP hF hind
  obtain ⟨hnpos,hnsize,hconf⟩ := hN (Fintype.card V) hn
  have hsize : T.card+k≤Fintype.card V := by omega
  have hh := rootedSubset_dense_conflict_free_card P F T k hsize hk2 δ α L hα hP hF hind
    (by simpa only [hT] using hroots)
  dsimp only at hh
  simp only [hT] at hh
  have hhalf : (1/2:ℝ)≤1-2*(s+k:ℝ)*Real.exp (-α^2*(s+k:ℝ)/8)-
      L*(2*(s:ℝ)*((k:ℝ)/(Fintype.card V-s:ℕ))+Fintype.card V*((k:ℝ)/(Fintype.card V-s:ℕ))^2) := by
    linarith only [hfailure,hconf]
  calc
    _ = (1/2:ℝ)*((Fintype.card V:ℝ)^k/((2:ℝ)^k*k.factorial)) := by rw [pow_succ];ring
    _ ≤ (1/2:ℝ)*((Fintype.card V-s).choose k:ℝ) :=
      mul_le_mul_of_nonneg_left (choose_rooted_power_lower (Fintype.card V) s k hnsize) (by norm_num)
    _ ≤ _ := (mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)).trans hh

end Oberwolfach
