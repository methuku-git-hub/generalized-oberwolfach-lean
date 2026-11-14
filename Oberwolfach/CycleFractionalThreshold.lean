module

public import Oberwolfach.DivisibleComplementColouring
public import Oberwolfach.IntegralFractionalBridge
public import Oberwolfach.TwoComponentLower

@[expose] public section

/-! The ordinary integral cycle threshold also suffices for fractional
cycle decompositions without divisibility assumptions. The random colouring,
residue repair, parity switches and averaging are all proved dependencies. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem large_even_multiple_reciprocal (r : ℕ) (hr : 0<r) (α : ℝ) (hα : 0<α) :
    ∃ q : ℕ,0<q ∧ Even q ∧ r∣q ∧ 1/(q+1:ℝ)<α/4 := by
  let k : ℕ := ⌈4/α⌉₊+1
  let q := 2*r*k
  have hk : 0<k := by dsimp [k];omega
  have hq : 0<q := by dsimp [q];positivity
  refine ⟨q,hq,?_,?_,?_⟩
  · refine ⟨r*k,?_⟩
    dsimp [q]
    ring
  · refine ⟨2*k,?_⟩
    dsimp [q]
    ring
  · have hkr : 4/α<(k:ℝ) := by
      have hh := Nat.le_ceil (4/α)
      dsimp [k]
      push_cast
      linarith
    have hkq : k≤q := by
      dsimp [q]
      nlinarith
    have hqr : 4/α<(q:ℝ)+1 := by
      have hh : (k:ℝ)≤q := by exact_mod_cast hkq
      linarith
    have hm := (div_lt_iff₀ hα).mp hqr
    apply (div_lt_iff₀ (show (0:ℝ)<q+1 by positivity)).mpr
    nlinarith

theorem edgeColourGraph_partition {n k : ℕ} (G : SimpleGraph (Fin n))
    (σ : Sym2 (Fin n) → Fin k) : EdgePartition G (edgeColourGraph G σ) := by
  intro u v
  constructor
  · constructor
    · intro huv
      exact ⟨σ s(u,v),huv,rfl⟩
    · rintro ⟨a,ha⟩
      exact ha.1
  · intro a b ha hb
    exact ha.2.symm.trans hb.2

theorem cycle_fractional_positive_margin (r : ℕ) (hr : 3≤r) (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ n≥N,∀ G : SimpleGraph (Fin n),
      (∀ v,(cycleThreshold r+α)*(n:ℝ)≤(G.degree v:ℝ)) →
      HasFractionalDecomposition G (fun H => IsEmbeddedCycle H r) := by
  obtain ⟨q,hq,hqeven,hrq,hqsmall⟩ := large_even_multiple_reciprocal r (by omega) α hα
  let ξ := min (α/8) (1/(2*(q+1:ℝ)))
  have hξ : 0<ξ := lt_min (by positivity) (by positivity)
  have hξsmall : ξ≤1/(q+1:ℝ) := by
    have hq1 : (0:ℝ)<q+1 := by positivity
    have hh := min_le_right (α/8) (1/(2*(q+1:ℝ)))
    have hc : 1/(2*(q+1:ℝ))≤1/(q+1:ℝ) := by
      apply one_div_le_one_div_of_le hq1
      linarith
    exact hh.trans hc
  have hloss : 1/(q+1:ℝ)+ξ<α/2 := by
    have hh := min_le_left (α/8) (1/(2*(q+1:ℝ)))
    dsimp only [ξ]
    linarith only [hh,hqsmall,hα]
  obtain ⟨N₁,hN₁⟩ := dense_divisible_complement_colouring q r hqeven (by omega) hrq α ξ hα hξ hξsmall
  obtain ⟨N₂,hN₂⟩ := cycleThreshold_positive_margin r (α:=α/2) (by positivity)
  refine ⟨max N₁ N₂,?_⟩
  intro n hn G hdeg
  have hdense (v : Fin n) : (1/2+α)*Fintype.card (Fin n)≤(G.degree v:ℝ) := by
    simp only [Fintype.card_fin]
    have hh := mul_le_mul_of_nonneg_right (cycleThreshold_half_le hr) (Nat.cast_nonneg (α:=ℝ) n)
    nlinarith [hdeg v]
  obtain ⟨τ,hdiv,hτdeg⟩ := hN₁ (Fin n) (by simpa only [Fintype.card_fin] using (le_max_left _ _).trans hn) G hdense
  have hdec (a : Fin (q+1)) : HasCycleDecomposition (G\edgeColourGraph G τ a) r := by
    apply hN₂ n ((le_max_right _ _).trans hn) (G\edgeColourGraph G τ a)
    · simpa only [CycleDivisible,← SimpleGraph.card_neighborSet_eq_degree,
        SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hdiv a
    · intro v
      have hc := congrArg (fun t : ℕ => (t:ℝ))
        (degree_complement_add G (edgeColourGraph G τ a) (edgeColourGraph_le G τ a) v)
      simp only [Nat.cast_add] at hc
      have hJ := hτdeg a v
      simp only [Fintype.card_fin] at hJ
      have hDn : (G.degree v:ℝ)≤n := by
        exact_mod_cast (by simpa only [Fintype.card_fin] using (G.degree_lt_card_verts v).le)
      have hDdiv := div_le_div_of_nonneg_right hDn (show (0:ℝ)≤q+1 by positivity)
      have hsmall := mul_le_mul_of_nonneg_right hloss.le (Nat.cast_nonneg (α:=ℝ) n)
      have he : (1/(q+1:ℝ)+ξ)*n=(n:ℝ)/(q+1:ℝ)+ξ*n := by ring
      rw [he] at hsmall
      have hG := hdeg v
      simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hc hJ hDdiv hG ⊢
      nlinarith only [hc,hJ,hDdiv,hsmall,hG]
  exact fractionalDecomposition_of_divisible_complements G (edgeColourGraph G τ) (by omega)
    (edgeColourGraph_partition G τ) hdec

end Oberwolfach
