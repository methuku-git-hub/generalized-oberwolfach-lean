module

public import Oberwolfach.DisjointConfigurationSelection
public import Oberwolfach.AsymptoticMargins

@[expose] public section

/-! Uniform order and constant choices for a sparse disjoint absorber
reservoir. The fixed configuration family and all compatibility sets may
vary with the host; the constants do not. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem configuration_reservoir_order (h c : ℕ) (K K' a L δ : ℝ)
    (hK : 0 < K) (hK' : 0 < K') (ha : 0 < a) (hL : 0 < L) (hδ : 0 < δ) :
    ∃ γ : ℝ,0 < γ ∧ ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n →
    ∀ (C I E : Type*) [Fintype C] [Fintype I] [DecidableEq C] [DecidableEq E],
    ∀ (A : C → Finset E) (T : I → Finset C) (P : Finset (C×C)),
      (∀ z∈P,z.1≠z.2) →
      (∀ a b,a≠b → ¬Disjoint (A a) (A b) → (a,b)∈P) →
      (∀ j,(A j).card ≤ h+1) →
      (Fintype.card C:ℝ) ≤ K*(n:ℝ)^(h+1) →
      (P.card:ℝ) ≤ K'*(n:ℝ)^(2*h+1) →
      (Fintype.card I:ℝ) ≤ L*(n:ℝ)^c →
      (∀ i,a*(n:ℝ)^(h+1) ≤ (T i).card) →
    ∃ S : Finset C,((S.biUnion A).card:ℝ) ≤ δ*n ∧
      (∀ j∈S,∀ k∈S,j≠k → Disjoint (A j) (A k)) ∧
      ∀ i,γ*n ≤ ((S∩T i).card:ℝ) := by
  let ρ := min 1 (min (δ/(4*(h+1)*K)) (a/(32*K')))
  have hρ : 0 < ρ := by dsimp [ρ];positivity
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρδ : ρ ≤ δ/(4*(h+1)*K) := (min_le_right _ _).trans (min_le_left _ _)
  have hρa : ρ ≤ a/(32*K') := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall₁ : 4*(h+1)*K*ρ ≤ δ := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ)<4*(h+1)*K)).mp hρδ
    nlinarith only [hh]
  have hsmall₂ : 32*K'*ρ ≤ a := by
    have hh := (le_div_iff₀ (by positivity : 0<32*K')).mp hρa
    nlinarith only [hh]
  obtain ⟨n₁,hn₁⟩ := eventually_stretchedExp_le_inv_pow (2*L) c
    (c:=ρ*a/12) (p:=1) (by positivity) (by norm_num) 1
  refine ⟨a*ρ/4,by positivity,max n₁ 3,?_⟩
  intro n hn C I E _ _ _ _ A T P hP hconflict hA hC hPairs hI hT
  have hn3 : 3 ≤ n := (le_max_right _ _).trans hn
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hnR1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  let p := ρ/(n:ℝ)^h
  let u := K*ρ*n
  let v := K'*ρ^2*n
  have hp : 0 ≤ p := by dsimp [p];positivity
  have hp1 : p ≤ 1 := by
    apply (div_le_one (pow_pos hnR _)).mpr
    exact hρ1.trans (one_le_pow₀ hnR1)
  have hu : 0 < u := by dsimp [u];positivity
  have hv : 0 < v := by dsimp [v];positivity
  have hpow₁ : p*(n:ℝ)^(h+1)=ρ*n := by
    dsimp [p]
    rw [pow_succ]
    field_simp
  have hpow₂ : p^2*(n:ℝ)^(2*h+1)=ρ^2*n := by
    dsimp [p]
    rw [show 2*h+1=(h+h)+1 by omega,pow_succ (n:ℝ) (h+h),pow_add]
    field_simp
    <;> ring
  have hs : p*Fintype.card C ≤ u := by
    calc
      _ ≤ p*(K*(n:ℝ)^(h+1)) := mul_le_mul_of_nonneg_left hC hp
      _ = K*(p*(n:ℝ)^(h+1)) := by ring
      _ = _ := by rw [hpow₁];dsimp [u];ring
  have hps : p^2*P.card ≤ v := by
    calc
      _ ≤ p^2*(K'*(n:ℝ)^(2*h+1)) := mul_le_mul_of_nonneg_left hPairs (sq_nonneg p)
      _ = K'*(p^2*(n:ℝ)^(2*h+1)) := by ring
      _ = _ := by rw [hpow₂];dsimp [v];ring
  have hmean (i : I) : ρ*a*n ≤ p*(T i).card := by
    have hh := mul_le_mul_of_nonneg_left (hT i) hp
    have heq : p*(a*(n:ℝ)^(h+1))=ρ*a*n := by
      calc
        _ = a*(p*(n:ℝ)^(h+1)) := by ring
        _ = _ := by rw [hpow₁];ring
    rwa [heq] at hh
  have htail := hn₁ n ((le_max_left _ _).trans hn)
  simp only [Real.rpow_natCast,Real.rpow_one,pow_one] at htail
  have hfailure : ∑ i : I,2*Real.exp (-p*(T i).card/12)<1/2 := by
    calc
      _ ≤ ∑ _i : I,2*Real.exp (-(ρ*a/12)*(n:ℝ)) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hmean i])) (by norm_num)
      _ = (Fintype.card I:ℝ)*(2*Real.exp (-(ρ*a/12)*(n:ℝ))) := by simp
      _ ≤ (L*(n:ℝ)^c)*(2*Real.exp (-(ρ*a/12)*(n:ℝ))) := mul_le_mul_of_nonneg_right hI (by positivity)
      _ = (2*L)*(n:ℝ)^c*Real.exp (-(ρ*a/12)*(n:ℝ)) := by ring
      _ ≤ 1/(n:ℝ) := htail
      _ < 1/2 := by
        apply (div_lt_iff₀ hnR).mpr
        have hh : (3:ℝ) ≤ n := by exact_mod_cast hn3
        linarith
  obtain ⟨S,hS,hdisj,hcompat⟩ := disjoint_configuration_selection_finite A T P hP hconflict
    p u v hp hp1 hu hv hs hps hfailure
  refine ⟨S,?_,hdisj,?_⟩
  · have hcard : (S.biUnion A).card ≤ S.card*(h+1) := by
      calc
        _ ≤ ∑ j∈S,(A j).card := Finset.card_biUnion_le
        _ ≤ ∑ _j∈S,(h+1) := Finset.sum_le_sum (fun j _ => hA j)
        _ = _ := by simp
    have hc : ((S.biUnion A).card:ℝ) ≤ (S.card:ℝ)*(h+1) := by exact_mod_cast hcard
    have hs' := mul_le_mul_of_nonneg_right hS (by positivity : (0:ℝ) ≤ h+1)
    have hm := mul_le_mul_of_nonneg_right hsmall₁ hnR.le
    dsimp [u] at hs'
    nlinarith only [hc,hs',hm]
  · intro i
    have hh := hcompat i
    have hm := mul_le_mul_of_nonneg_right hsmall₂ (mul_nonneg hρ.le hnR.le)
    have hi := hmean i
    dsimp [v] at hh
    nlinarith only [hh,hm,hi]

end Oberwolfach
