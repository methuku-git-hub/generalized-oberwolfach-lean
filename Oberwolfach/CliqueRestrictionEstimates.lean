module

public import Oberwolfach.DisjointCliqueRestrictions
public import Oberwolfach.FiniteProductPerturbation
public import Oberwolfach.EqualizedColourRetention

@[expose] public section

/-! Quantitative costs of restricting clique vertex sets. The probability
law and all tentative lists remain fixed under these restrictions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem equalizedColour_probability_at
    {V C : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (L : V → Finset C) (hL : ∀ v,(L v).Nonempty)
    {l K : ℕ} (hl : 0<l) (hcard : ∀ v,(L v).card=l)
    (v : V) (c : C) (hc : c∈L v)
    (hbound : (colourNeighbourSet G L v c).card≤K) :
    (FiniteLaw.pi (fun u=>(FiniteLaw.uniformOn (L u) (hL u)).withCoin
      (equalizationCoin G L l K u) (equalizationCoin_bounds G L hl K u))).probability
      (fun σ=>coinRetainedColour G σ v=some c)=
      ((1-1/(l : ℝ))^K)/(l : ℝ) := by
  classical
  rw [coinRetainedColour_probability,uniformList_avoidance_product G L hL hcard]
  simp only [FiniteLaw.uniformOn,hc,ite_true,hcard,equalizationCoin]
  rw [mul_assoc,← pow_add,Nat.sub_add_cancel hbound]
  ring

theorem finiteLaw_clique_restriction_uniform_loss
    {V C J : Type*} [Fintype V] [Fintype C] [Fintype J]
    (G : SimpleGraph V) (μ : FiniteLaw (V → C×Bool))
    (T T' : J → Finset V) (hsub : ∀ j,T' j⊆T j) (c : C)
    {d : ℕ} {p : ℝ} (hp : 0≤p)
    (hloss : ∀ j,((T j)\(T' j)).card≤d)
    (hpoint : ∀ j,∀ v∈T j,μ.probability (fun σ=>coinRetainedColour G σ v=some c)≤p) :
    0≤μ.probability (fun σ=>∀ j,∃ v∈T j,coinRetainedColour G σ v=some c)-
      μ.probability (fun σ=>∀ j,∃ v∈T' j,coinRetainedColour G σ v=some c) ∧
    μ.probability (fun σ=>∀ j,∃ v∈T j,coinRetainedColour G σ v=some c)-
      μ.probability (fun σ=>∀ j,∃ v∈T' j,coinRetainedColour G σ v=some c)≤
      (Fintype.card J : ℝ)*(d : ℝ)*p := by
  classical
  have hh := finiteLaw_clique_restriction_loss G μ Finset.univ T T' (fun j _=>hsub j) c
  simp only [Finset.mem_univ,forall_const] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  calc
    _ ≤ ∑ j : J,(d : ℝ)*p := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ∑ _v∈T j\T' j,p := Finset.sum_le_sum (fun v hv=>hpoint j v (Finset.mem_sdiff.mp hv).1)
        _ = (((T j)\T' j).card : ℝ)*p := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hloss j) hp
    _ = _ := by simp;ring

theorem finiteFamily_restriction_product_loss
    {J : Type*} [Fintype J] (m m' : J → ℕ) {l d : ℕ} (hl : 0<l)
    (hsub : ∀ j,m' j≤m j) (hsize : ∀ j,m j≤l)
    (hloss : ∀ j,m j-m' j≤d) {r : ℝ} (hr : 0≤r ∧ r≤1/(l : ℝ)) :
    0≤(∏ j,(m j : ℝ)*r)-(∏ j,(m' j : ℝ)*r) ∧
      (∏ j,(m j : ℝ)*r)-(∏ j,(m' j : ℝ)*r)≤
        (Fintype.card J : ℝ)*(d : ℝ)/(l : ℝ) := by
  classical
  have hlr : (0 : ℝ)<l := by exact_mod_cast hl
  have hfac (j : J) : 0≤(m' j : ℝ)*r ∧ (m' j : ℝ)*r≤(m j : ℝ)*r ∧ (m j : ℝ)*r≤1 := by
    refine ⟨mul_nonneg (Nat.cast_nonneg _) hr.1,
      mul_le_mul_of_nonneg_right (by exact_mod_cast hsub j) hr.1,?_⟩
    calc
      _ ≤ (m j : ℝ)*(1/(l : ℝ)) := mul_le_mul_of_nonneg_left hr.2 (Nat.cast_nonneg _)
      _ ≤ (l : ℝ)*(1/(l : ℝ)) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast hsize j) (by positivity)
      _ = 1 := by field_simp
  have hh := finite_product_perturbation Finset.univ (fun j=>(m j : ℝ)*r)
    (fun j=>(m' j : ℝ)*r) (fun j _=>hfac j)
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hterm (j : J) : (m j : ℝ)*r-(m' j : ℝ)*r≤(d : ℝ)/(l : ℝ) := by
    have he : ((m j-m' j : ℕ) : ℝ)=(m j : ℝ)-(m' j : ℝ) := Nat.cast_sub (hsub j)
    calc
      _ = ((m j-m' j : ℕ) : ℝ)*r := by rw [he];ring
      _ ≤ (d : ℝ)*r := mul_le_mul_of_nonneg_right (by exact_mod_cast hloss j) hr.1
      _ ≤ (d : ℝ)*(1/(l : ℝ)) := mul_le_mul_of_nonneg_left hr.2 (Nat.cast_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∑ _j : J,(d : ℝ)/(l : ℝ) := Finset.sum_le_sum (fun j _=>hterm j)
    _ = _ := by simp;ring

end Oberwolfach
