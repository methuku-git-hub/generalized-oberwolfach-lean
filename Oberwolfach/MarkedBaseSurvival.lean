module

public import Oberwolfach.MarkedBasePhysical

@[expose] public section

/-! Concentration of the actual physical survival sum for marked base
cycles. A conservative one-vertex incidence bound gives an exponential
linear tail, sufficient for a polynomial union over hub pairs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (b m : ℕ) (T₀ TK : Finset V)

def markedBaseSurvivalSum (σ : Sym2 V→Option (Bool×Bool)) : ℝ :=
  ∑ C : DenseMarkedBaseFamily P π b m T₀ TK,
    (1/(Fintype.card V:ℝ)^(m+1))*patternValue (markedBaseRequiredEdges P π b m T₀ TK C)
      (markedBaseRequiredState P π b m T₀ TK C) σ

theorem markedBase_family_total : (Fintype.card (DenseMarkedBaseFamily P π b m T₀ TK):ℝ)≤
    (Fintype.card V:ℝ)^(m+1) := by
  have hh := Fintype.card_subtype_le (DenseMarkedBase P π b T₀ TK (m:=m))
  simp only [Fintype.card_fun,Fintype.card_fin] at hh
  exact_mod_cast hh

theorem markedBase_normalized_edge_load (hn : 0<Fintype.card V) (e : Sym2 V) :
    (∑ C : DenseMarkedBaseFamily P π b m T₀ TK,
      if e∈markedBaseRequiredEdges P π b m T₀ TK C then 1/(Fintype.card V:ℝ)^(m+1) else 0)≤
        2*((m:ℝ)+1)/Fintype.card V := by
  have hn0 : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have he (C : DenseMarkedBaseFamily P π b m T₀ TK) :
      (if e∈markedBaseRequiredEdges P π b m T₀ TK C then 1/(Fintype.card V:ℝ)^(m+1) else 0)=
        (if e∈markedBaseRequiredEdges P π b m T₀ TK C then (1:ℝ) else 0)/(Fintype.card V:ℝ)^(m+1) := by
    split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_div]
  apply (div_le_div_of_nonneg_right (markedBase_edge_incidence P π b m T₀ TK e) (by positivity)).trans
  apply le_of_eq
  rw [pow_succ]
  field_simp

theorem markedBaseSurvivalSum_tail (hn : 0<Fintype.card V) (hb : 1≤b) (hm : 2≤m)
    (μ : Sym2 V→FiniteLaw (Option (Bool×Bool))) (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μ).probability (fun σ=>t≤
      |markedBaseSurvivalSum P π b m T₀ TK σ-
        ∑ C : DenseMarkedBaseFamily P π b m T₀ TK,
          (1/(Fintype.card V:ℝ)^(m+1))*∏ e∈markedBaseRequiredEdges P π b m T₀ TK C,
            (μ e).mass (markedBaseRequiredState P π b m T₀ TK C e)|)≤
      2*Real.exp (-2*t^2/(2*((m:ℝ)+1)^2/Fintype.card V)) := by
  have htotal : (∑ _ : DenseMarkedBaseFamily P π b m T₀ TK,1/(Fintype.card V:ℝ)^(m+1))≤1 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one_div]
    exact (div_le_one (by positivity)).mpr (markedBase_family_total P π b m T₀ TK)
  have hh := independent_pattern_sum_tail μ (markedBaseRequiredEdges P π b m T₀ TK)
    (fun _ : DenseMarkedBaseFamily P π b m T₀ TK=>1/(Fintype.card V:ℝ)^(m+1))
    (by intro C;positivity) (markedBaseRequiredState P π b m T₀ TK)
    (2*((m:ℝ)+1)/Fintype.card V) ((m:ℝ)+1) 1 (by positivity) (by positivity) (by norm_num)
    (by intro C;exact_mod_cast (markedBaseRequiredEdges_card P π b m T₀ TK hb hm C).le)
    htotal (markedBase_normalized_edge_load P π b m T₀ TK hn) t ht
  have he : (2*((m:ℝ)+1)/Fintype.card V)*((m:ℝ)+1)*1=2*((m:ℝ)+1)^2/Fintype.card V := by ring
  simpa only [he,markedBaseSurvivalSum] using hh

theorem markedBaseSurvivalSum_lower_tail (hn : 0<Fintype.card V) (hb : 1≤b) (hm : 2≤m)
    (p k pstar c t : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (hstar : 0≤pstar) (hstar1 : pstar≤1) (hplo : pstar≤p) (hklo : pstar≤k) (ht : 0<t)
    (hmany : c*(Fintype.card V:ℝ)^(m+1)≤Fintype.card (DenseMarkedBaseFamily P π b m T₀ TK)) :
    (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
      (fun σ=>markedBaseSurvivalSum P π b m T₀ TK σ≤pstar^(m+1)*c-t)≤
      2*Real.exp (-2*t^2/(2*((m:ℝ)+1)^2/Fintype.card V)) := by
  let w := 1/(Fintype.card V:ℝ)^(m+1)
  let μ := markedPhysicalLaw p k hp hk hsum
  have hprod (C : DenseMarkedBaseFamily P π b m T₀ TK) :
      pstar^(m+1)≤∏ e∈markedBaseRequiredEdges P π b m T₀ TK C,
        μ.mass (markedBaseRequiredState P π b m T₀ TK C e) :=
    pattern_survival_product_lower _ _ pstar hstar hstar1
      (markedBaseRequiredState_mass_lower P π b m T₀ TK hb hm p k pstar hp hk hsum hplo hklo C)
      (m+1) (markedBaseRequiredEdges_card P π b m T₀ TK hb hm C).le
  have htotal : c≤∑ _ : DenseMarkedBaseFamily P π b m T₀ TK,w := by
    simp only [w,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one_div]
    exact (le_div_iff₀ (by positivity)).mpr hmany
  have hmean : pstar^(m+1)*c≤∑ C : DenseMarkedBaseFamily P π b m T₀ TK,
      w*∏ e∈markedBaseRequiredEdges P π b m T₀ TK C,
        μ.mass (markedBaseRequiredState P π b m T₀ TK C e) := by
    apply (mul_le_mul_of_nonneg_left htotal (pow_nonneg hstar _)).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro C _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hprod C) (show 0≤w by dsimp [w];positivity)
  apply le_trans _ (markedBaseSurvivalSum_tail P π b m T₀ TK hn hb hm (fun _=>μ) t ht)
  apply finiteLaw_probability_mono
  intro σ hσ
  have hh := neg_le_abs (markedBaseSurvivalSum P π b m T₀ TK σ-
    ∑ C : DenseMarkedBaseFamily P π b m T₀ TK,w*∏ e∈markedBaseRequiredEdges P π b m T₀ TK C,
      μ.mass (markedBaseRequiredState P π b m T₀ TK C e))
  change t≤|markedBaseSurvivalSum P π b m T₀ TK σ-
    ∑ C : DenseMarkedBaseFamily P π b m T₀ TK,w*∏ e∈markedBaseRequiredEdges P π b m T₀ TK C,
      μ.mass (markedBaseRequiredState P π b m T₀ TK C e)|
  linarith only [hh,hmean,hσ]

end Oberwolfach
