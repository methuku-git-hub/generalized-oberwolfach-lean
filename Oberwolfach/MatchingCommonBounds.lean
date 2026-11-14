module

public import Oberwolfach.FiniteWeightedHypergraphMatching

@[expose] public section

/-! One numerical margin controls the unions over all fixed tests and roots.
The test family is quantified before any of the random partitions. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem matching_failure_sums
    (V I C A : Type) [Fintype V] [Fintype I] [Fintype C] [Fintype A] [Nonempty I]
    (N z : ℝ) (hN : 1≤N)
    (hV : (Fintype.card V : ℝ)≤N) (hC : (Fintype.card C : ℝ)≤N)
    (hA : (Fintype.card A : ℝ)≤N)
    (f₀ : V → ℝ) (f₁ f₄ f₅ : A → ℝ) (f₂ f₃ : ℝ)
    (hf₀ : ∀ v,f₀ v≤z) (hf₁ : ∀ a,f₁ a≤z) (hf₂ : f₂≤z) (hf₃ : f₃≤z)
    (hf₄ : ∀ a,f₄ a≤z) (hf₅ : ∀ a,f₅ a≤z)
    (hsmall : 10*(Fintype.card I : ℝ)*N^3*Real.exp z<1) :
    ((∑ v : V,∑ _i : I,2*Real.exp (f₀ v))+(∑ a : A,∑ _i : I,2*Real.exp (f₁ a))<1) ∧
    ((∑ _i : I,∑ _v : V,∑ _c : C,Real.exp f₂)+
      ((∑ _i : I,∑ _v : V,∑ _u : V,∑ _c : C,Real.exp f₃)+
        (∑ _i : I,∑ a : A,∑ _c : C,Real.exp (f₄ a)))<1) ∧
    (∑ a : A,2*Real.exp (f₅ a))<1 := by
  have hp : (1 : ℝ)≤Fintype.card I := by exact_mod_cast Fintype.card_pos (α:=I)
  have he : 0<Real.exp z := Real.exp_pos _
  have hn2 : N≤N^2 := by nlinarith
  have hn3 : N≤N^3 := by nlinarith [mul_le_mul_of_nonneg_left hn2 (show 0≤N by linarith)]
  have hn23 : N^2≤N^3 := by nlinarith [mul_le_mul_of_nonneg_left hn2 (show 0≤N by linarith)]
  have hs₀ : (∑ v : V,∑ _i : I,2*Real.exp (f₀ v))≤2*(Fintype.card I : ℝ)*N^3*Real.exp z := by
    calc
      _ ≤ ∑ _v : V,∑ _i : I,2*Real.exp z := by gcongr with v _ i _;exact hf₀ v
      _ = 2*(Fintype.card I : ℝ)*Fintype.card V*Real.exp z := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
      _ ≤ _ := by gcongr;exact hV.trans hn3
  have hs₁ : (∑ a : A,∑ _i : I,2*Real.exp (f₁ a))≤2*(Fintype.card I : ℝ)*N^3*Real.exp z := by
    calc
      _ ≤ ∑ _a : A,∑ _i : I,2*Real.exp z := by gcongr with a _ i _;exact hf₁ a
      _ = 2*(Fintype.card I : ℝ)*Fintype.card A*Real.exp z := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
      _ ≤ _ := by gcongr;exact hA.trans hn3
  have hs₂ : (∑ _i : I,∑ _v : V,∑ _c : C,Real.exp f₂)≤(Fintype.card I : ℝ)*N^3*Real.exp z := by
    calc
      _ ≤ ∑ _i : I,∑ _v : V,∑ _c : C,Real.exp z := by gcongr
      _ = (Fintype.card I : ℝ)*((Fintype.card V : ℝ)*Fintype.card C)*Real.exp z := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
      _ ≤ _ := by
        gcongr
        calc
          _ ≤ N*N := mul_le_mul hV hC (Nat.cast_nonneg _) (by linarith)
          _ ≤ N^3 := by nlinarith
  have hs₃ : (∑ _i : I,∑ _v : V,∑ _u : V,∑ _c : C,Real.exp f₃)≤(Fintype.card I : ℝ)*N^3*Real.exp z := by
    calc
      _ ≤ ∑ _i : I,∑ _v : V,∑ _u : V,∑ _c : C,Real.exp z := by gcongr
      _ = (Fintype.card I : ℝ)*((Fintype.card V : ℝ)*Fintype.card V*Fintype.card C)*Real.exp z := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
      _ ≤ _ := by
        gcongr
        calc
          _ ≤ N*N*N := by gcongr
          _ = N^3 := by ring
  have hs₄ : (∑ _i : I,∑ a : A,∑ _c : C,Real.exp (f₄ a))≤(Fintype.card I : ℝ)*N^3*Real.exp z := by
    calc
      _ ≤ ∑ _i : I,∑ _a : A,∑ _c : C,Real.exp z := by gcongr with i _ a _ c _;exact hf₄ a
      _ = (Fintype.card I : ℝ)*((Fintype.card A : ℝ)*Fintype.card C)*Real.exp z := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
      _ ≤ _ := by
        gcongr
        calc
          _ ≤ N*N := mul_le_mul hA hC (Nat.cast_nonneg _) (by linarith)
          _ ≤ N^3 := by nlinarith
  have hs₅ : (∑ a : A,2*Real.exp (f₅ a))≤2*(Fintype.card I : ℝ)*N^3*Real.exp z := by
    calc
      _ ≤ ∑ _a : A,2*Real.exp z := by gcongr with a _;exact hf₅ a
      _ = 2*(1 : ℝ)*Fintype.card A*Real.exp z := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
      _ ≤ _ := by gcongr;exact hA.trans hn3
  have hbase : 0≤(Fintype.card I : ℝ)*N^3*Real.exp z := by positivity
  constructor
  · nlinarith
  constructor <;> nlinarith

end Oberwolfach
