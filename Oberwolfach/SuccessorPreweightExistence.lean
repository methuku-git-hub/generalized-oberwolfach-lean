module

public import Oberwolfach.SuccessorPreweights
public import Oberwolfach.SuccessorParameterChoice
public import Oberwolfach.SuccessorOrderMargins
public import Oberwolfach.SuccessorCyclicMargin

@[expose] public section

/-! The preliminary weighting with the manuscript quantifier order:
positive weight constants precede the approximation tolerance; the graph
order threshold precedes the graph and permutation. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def successorWeightLower (k : ℕ) (β : ℝ) : ℝ :=
  ((k+2 : ℝ) * cyclicSectorLower k (β/2)) / 8

def successorWeightUpper (k : ℕ) (β : ℝ) : ℝ :=
  ((k+2 : ℝ) * cyclicSectorUpper k (β/2)) * (2*(2*(k+2 : ℝ))) ^ (2*(k+2))

theorem successorWeightConstants_pos (k : ℕ) (β : ℝ) (hβ : 0 < β) :
    0 < successorWeightLower k β ∧ 0 < successorWeightUpper k β := by
  obtain ⟨hl,hu⟩ := cyclicSectorConstants_pos k (β/2) (by positivity)
  unfold successorWeightLower successorWeightUpper
  constructor <;> positivity

theorem successor_preweight_existence (k : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∀ τ : ℝ, 0 < τ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [Nonempty V], N ≤ Fintype.card V →
      ∀ (G : SimpleGraph V) (π : Equiv.Perm V) (b : Fin (k+2) → Bool) (D : ℝ),
      (Fintype.card V : ℝ)/2 ≤ D → D ≤ 2*Fintype.card V →
      (∀ v, |(G.degree v : ℝ)-D| ≤ ε₀*Fintype.card V) →
      (∀ v, (successorCycleRatio k + β)*Fintype.card V ≤ (G.degree v : ℝ)) →
      ∃ w, SuccessorPreweightConditions G (fun i => choosePermutation π (b i)) D (τ/2) (τ/2)
        (successorWeightLower k β) (successorWeightUpper k β) w := by
  obtain ⟨C,η₀,hC,hη₀,hall⟩ := successor_preweights_quantitative (β/4) (by positivity)
  intro τ hτ
  let c := Fintype.card (Fin (k+2) ⊕ Fin (k+2))
  have hcval : c = 2*(k+2) := by simp only [c,Fintype.card_sum,Fintype.card_fin]; omega
  have hc : 0 < c := by omega
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  obtain ⟨η,ε₀,hη,hηsmall,hε₀,hεη,hs,hηβ,hsβ,hsτ,hpτ,hcp⟩ :=
    successor_small_parameters c C η₀ β τ hcR hC hη₀ hβ hτ
  obtain ⟨m₀,hm₀⟩ := hall η hη hηsmall
  obtain ⟨N,hN⟩ := successor_order_margins c m₀ hc η (τ/64) (min (β/4) (τ/32))
    hη (by positivity) (by positivity)
  refine ⟨ε₀,hε₀,N,?_⟩
  intro V _ _ hn G π b D hD hDup hnear hminG
  let n := Fintype.card V
  let m := n/c
  let d := equalCellSizes n c
  let a := equalCellAssignment (Fin (k+2) ⊕ Fin (k+2))
  letI : Nonempty (FixedPartition V (c+1) d) := equalCellPartition_nonempty c
  obtain ⟨hn2,hmpos,hmlarge,hscale,hmrecip,hnrecip,hδ,hδtuple⟩ := hN n hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmβ : (1 : ℝ)/m ≤ β/4 := hmrecip.trans (min_le_left _ _)
  have hmτ : (1 : ℝ)/m ≤ τ/32 := hmrecip.trans (min_le_right _ _)
  have hnτ : (2 : ℝ)/n ≤ τ/32 := hnrecip.trans (min_le_right _ _)
  have hDmin := successor_mean_lower G D (successorCycleRatio k) β ε₀ hminG hnear
  obtain ⟨hmin,harg,hthreshold⟩ := successor_cyclic_numeric_inputs k n m D β ε₀ η hnR hmR hβ
    hDmin hD hηβ hs (by linarith)
  have hpnon : 0 ≤ C*Real.sqrt η := mul_nonneg hC.le (Real.sqrt_nonneg _)
  have hp1 : C*Real.sqrt η ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hc1 hpnon
    nlinarith
  have hm : ∀ s, d (a s) = m := equalCellAssignment_size _ n
  have hK : (n : ℝ) ≤ (2*c : ℝ)*m := by exact_mod_cast hscale
  have hcp' : 2*(k+2 : ℝ)*(C*Real.sqrt η) ≤ 1/2 := by
    have hcc : (c : ℝ) = 2*(k+2 : ℝ) := by exact_mod_cast hcval
    rw [← hcc]
    linarith
  have hδ' : 4*(2*(k+2 : ℝ))*n*Real.exp (-η^2*m/2) ≤
      (τ/64)*successorPairProbability m n := by
    simpa only [partitionFailure,m,hcval,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hδ
  have hδt' : 4*(2*(k+2 : ℝ))*n*Real.exp (-η^2*m/2) ≤ (1/2)*((m : ℝ)/n)^(2*(k+2)) := by
    simpa only [partitionFailure,m,hcval,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hδtuple
  obtain ⟨w,hw⟩ := hm₀ V k (c+1) d G π b a m hm hmpos hmlarge hn2 (Nat.div_le_self n c)
    D ε₀ (β/2) (τ/64) (τ/2) (2*c) (by positivity) (by positivity) hD hDup hεη hnear hmin hK
    hthreshold harg hp1 hcp' (by linarith) hδ' hδt'
  refine ⟨w,⟨hw.nonneg,hw.invalid_zero,?_,hw.lower,?_,?_,hw.positions⟩⟩
  · intro t
    have hh : (2*c : ℝ) = 2*(2*(k+2 : ℝ)) := by rw [hcval]; push_cast; ring
    simpa only [hh,successorWeightUpper] using hw.upper t
  · intro i x y hxy hG
    obtain ⟨hl,hu⟩ := hw.left i x y hxy hG
    exact ⟨by linarith,hu⟩
  · intro i x y hxy hG
    obtain ⟨hl,hu⟩ := hw.right i x y hxy hG
    exact ⟨by linarith,hu⟩

end Oberwolfach
