module

public import Oberwolfach.DivisibleColourRepair
public import Oberwolfach.DivisibilityUniformSample
public import Oberwolfach.DivisibilityRepairScales

@[expose] public section

/-! Dense graphs admit an edge colouring whose every complement is divisible,
with degree loss close to the reciprocal number of colours. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
universe u
attribute [local instance] Classical.propDecidable

theorem dense_divisible_complement_colouring (q h : ℕ) (hq : Even q) (hh : 0<h) (hhq : h∣q)
    (ε ξ : ℝ) (hε : 0<ε) (hξ : 0<ξ) (hξsmall : ξ≤1/(q+1:ℝ)) :
    ∃ N : ℕ,∀ (V : Type u) [Fintype V] [DecidableEq V],N≤Fintype.card V →
    ∀ G : SimpleGraph V,(∀ v,(1/2+ε)*Fintype.card V≤(G.degree v:ℝ)) →
    ∃ τ : Sym2 V → Fin (q+1),
      (∀ a,(∀ v,Even ((G\edgeColourGraph G τ a).degree v)) ∧
        h∣(G\edgeColourGraph G τ a).edgeFinset.card) ∧
      (∀ a v,((edgeColourGraph G τ a).degree v:ℝ)≤(G.degree v:ℝ)/(q+1:ℝ)+ξ*Fintype.card V) := by
  let ρ := ε/(q+1:ℝ)^2
  have hρ : 0<ρ := by dsimp [ρ];positivity
  obtain ⟨N₁,hN₁⟩ := divisibility_uniform_colour_sample (q+1) (by omega) ε ξ hε hξ
  obtain ⟨L,N₂,hL,hN₂⟩ := divisibility_repair_scales q h ρ ξ hρ hξ
  refine ⟨max N₁ N₂,?_⟩
  intro V instV instDec hn G hdeg
  obtain ⟨hnpos,hr,hlose,hpack,hchange⟩ := hN₂ (Fintype.card V) ((le_max_right _ _).trans hn)
  letI : Nonempty V := Fintype.card_pos_iff.mp hnpos
  have hnr : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hnpos
  obtain ⟨σ,hσdeg,hσpath⟩ := hN₁ V ((le_max_left _ _).trans hn) G hdeg (Fin.last q)
  have hreserve : q*h≤(edgeColourGraph G σ (Fin.last q)).edgeFinset.card := by
    let v : V := Classical.choice inferInstance
    have hD : (Fintype.card V:ℝ)/2≤(G.degree v:ℝ) := by
      have hh := hdeg v
      have he := mul_nonneg hε.le hnr.le
      nlinarith
    have hdiv := div_le_div_of_nonneg_right hD (show (0:ℝ)≤q+1 by positivity)
    have herr := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hξsmall hnr.le)
      (show (0:ℝ)≤4 by norm_num)
    have hs := (abs_lt.mp (hσdeg (Fin.last q) v)).1
    have hqne : (q:ℝ)+1≠0 := by positivity
    have hc : (q:ℝ)*h≤((edgeColourGraph G σ (Fin.last q)).degree v:ℝ) := by
      simp only [Nat.cast_add,Nat.cast_one] at hs
      have he1 : ((Fintype.card V:ℝ)/2)/(q+1:ℝ)=(Fintype.card V:ℝ)/(4*(q+1:ℝ))*2 := by field_simp [hqne] <;> ring
      have he2 : (1/(q+1:ℝ)*Fintype.card V)/4=(Fintype.card V:ℝ)/(4*(q+1:ℝ)) := by field_simp [hqne] <;> ring
      rw [he1] at hdiv
      rw [he2] at herr
      linarith only [hr,hdiv,herr,hs]
    have hcNat : q*h≤(edgeColourGraph G σ (Fin.last q)).degree v := by exact_mod_cast hc
    exact hcNat.trans ((edgeColourGraph G σ (Fin.last q)).degree_le_card_edgeFinset v)
  have hpath (a : Fin q) (u v : V) (huv : u≠v) : ρ*Fintype.card V≤
      (colouredTwoPathCount G σ u v a.castSucc (Fin.last q):ℝ) := by
    simpa only [ρ,Nat.cast_add,Nat.cast_one] using hσpath a.castSucc u v huv
  obtain ⟨τ,hdiv,hchg⟩ := divisible_colour_repair hq hh hhq G σ ρ L hL hreserve hpath hlose hpack
  refine ⟨τ,hdiv,?_⟩
  intro a v
  have hc := (abs_le.mp (hchg a v)).2
  have hs := (abs_lt.mp (hσdeg a v)).2
  simp only [Nat.cast_add,Nat.cast_one] at hs
  have hpos := mul_nonneg hξ.le hnr.le
  linarith only [hc,hs,hchange,hpos]

end Oberwolfach
