module

public import Oberwolfach.MarkedAssignedRowPacking

@[expose] public section

/-! Choose the free-use cap before the permutation radius and label
multiplicity. Their additive deletion costs are paid by the order threshold. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
noncomputable section
namespace Oberwolfach

theorem marked_row_packing_numeric_threshold (l : ℕ) (β A : ℝ) (hβ : 0<β) (hA : 0<A) :
    ∃ K : ℕ, 0<K ∧ ∀ b M : ℕ, ∃ n₀ : ℕ, ∀ n N : ℕ, n₀≤n →
      (N:ℝ)≤A*n → ∀ q : ℝ, q≤β*n/4 →
      q+(N*(l+4):ℕ)/(K:ℝ)+(l+5)*(2*b+1)+8*(K+2*M:ℕ)<β*n := by
  obtain ⟨K,hK⟩ := exists_nat_gt (max 1 (4*A*((l:ℝ)+4)/β))
  have hK1 : (1:ℝ)<K := (le_max_left _ _).trans_lt hK
  have hKpos : 0<K := by exact_mod_cast (show (0:ℝ)<K by linarith)
  have hKreal : (0:ℝ)<K := Nat.cast_pos.mpr hKpos
  have hKβ : 4*A*((l:ℝ)+4)<(K:ℝ)*β :=
    (div_lt_iff₀ hβ).mp ((le_max_right _ _).trans_lt hK)
  refine ⟨K,hKpos,?_⟩
  intro b M
  let C : ℝ := ((l:ℝ)+5)*(2*b+1)+8*(K+2*M:ℕ)
  obtain ⟨n₀,hn₀⟩ := exists_nat_gt (max 1 (4*C/β))
  refine ⟨n₀,?_⟩
  intro n N hn hN q hq
  have hnreal : (n₀:ℝ)≤n := Nat.cast_le.mpr hn
  have hnpos : (0:ℝ)<n := by
    have hh := (le_max_left _ _).trans_lt (hn₀.trans_le hnreal)
    linarith
  have hCn : C<β*n/4 := by
    have hh := (div_lt_iff₀ hβ).mp ((le_max_right _ _).trans_lt (hn₀.trans_le hnreal))
    nlinarith only [hh]
  have hdiv : (N*(l+4):ℕ)/(K:ℝ)≤β*n/4 := by
    apply (div_le_iff₀ hKreal).mpr
    have hnL := mul_le_mul_of_nonneg_right hN (by positivity : 0≤(l:ℝ)+4)
    have hkn := mul_lt_mul_of_pos_right hKβ hnpos
    push_cast
    nlinarith only [hnL,hkn]
  dsimp [C] at hCn
  nlinarith only [hq,hdiv,hCn,mul_pos hβ hnpos]

end Oberwolfach
