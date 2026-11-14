module

public import Oberwolfach.MarkedPathPattern

@[expose] public section

/-! Physical survival of actual common paths. The fixed roots remain
external to the free-coordinate domain, and no root spoke is sampled here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (b m : ℕ) (j : Bool) (T₀ TK : Finset V) (v v' : V)

def markedPathSurvivalSum (σ : Sym2 V→Option (Bool×Bool)) : ℝ :=
  ∑ C : DenseRootMarkedPathFamily P π b m j T₀ TK v v',
    (1/(Fintype.card V:ℝ)^(m+1))*patternValue (markedPathRequiredEdges P π b m j T₀ TK v v' C)
      (markedPathRequiredState P π b m j T₀ TK v v' C) σ

theorem markedPath_family_total : (Fintype.card (DenseRootMarkedPathFamily P π b m j T₀ TK v v'):ℝ)≤
    (Fintype.card V:ℝ)^(m+1) := by
  have hh := Fintype.card_subtype_le (DenseRootMarkedPath P π b j T₀ TK v v' (m:=m))
  simp only [Fintype.card_fun,Fintype.card_fin] at hh
  exact_mod_cast hh

theorem markedPath_normalized_edge_load (hn : 0<Fintype.card V) (e : Sym2 V) :
    (∑ C : DenseRootMarkedPathFamily P π b m j T₀ TK v v',
      if e∈markedPathRequiredEdges P π b m j T₀ TK v v' C then 1/(Fintype.card V:ℝ)^(m+1) else 0)≤
        2*((m:ℝ)+1)/Fintype.card V := by
  have hn0 : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have he (C : DenseRootMarkedPathFamily P π b m j T₀ TK v v') :
      (if e∈markedPathRequiredEdges P π b m j T₀ TK v v' C then 1/(Fintype.card V:ℝ)^(m+1) else 0)=
        (if e∈markedPathRequiredEdges P π b m j T₀ TK v v' C then (1:ℝ) else 0)/(Fintype.card V:ℝ)^(m+1) := by
    split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_div]
  apply (div_le_div_of_nonneg_right (markedPath_edge_incidence P π b m j T₀ TK v v' e) (by positivity)).trans
  apply le_of_eq
  rw [pow_succ]
  field_simp

theorem markedPathSurvivalSum_tail (hn : 0<Fintype.card V) (hb : 1≤b) (hm : 1≤m) (hvv' : v≠v')
    (μ : Sym2 V→FiniteLaw (Option (Bool×Bool))) (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μ).probability (fun σ=>t≤
      |markedPathSurvivalSum P π b m j T₀ TK v v' σ-
        ∑ C : DenseRootMarkedPathFamily P π b m j T₀ TK v v',
          (1/(Fintype.card V:ℝ)^(m+1))*∏ e∈markedPathRequiredEdges P π b m j T₀ TK v v' C,
            (μ e).mass (markedPathRequiredState P π b m j T₀ TK v v' C e)|)≤
      2*Real.exp (-2*t^2/(2*((m:ℝ)+1)*((m:ℝ)+4)/Fintype.card V)) := by
  have htotal : (∑ _ : DenseRootMarkedPathFamily P π b m j T₀ TK v v',1/(Fintype.card V:ℝ)^(m+1))≤1 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one_div]
    exact (div_le_one (by positivity)).mpr (markedPath_family_total P π b m j T₀ TK v v')
  have hh := independent_pattern_sum_tail μ (markedPathRequiredEdges P π b m j T₀ TK v v')
    (fun _ : DenseRootMarkedPathFamily P π b m j T₀ TK v v'=>1/(Fintype.card V:ℝ)^(m+1))
    (by intro C;positivity) (markedPathRequiredState P π b m j T₀ TK v v')
    (2*((m:ℝ)+1)/Fintype.card V) ((m:ℝ)+4) 1 (by positivity) (by positivity) (by norm_num)
    (by intro C;exact_mod_cast (markedPathRequiredEdges_card P π b m j T₀ TK v v' hb hm hvv' C).le)
    htotal (markedPath_normalized_edge_load P π b m j T₀ TK v v' hn) t ht
  have he : (2*((m:ℝ)+1)/Fintype.card V)*((m:ℝ)+4)*1=2*((m:ℝ)+1)*((m:ℝ)+4)/Fintype.card V := by ring
  simpa only [he,markedPathSurvivalSum] using hh

theorem markedPathSurvivalSum_lower_tail (hn : 0<Fintype.card V) (hb : 1≤b) (hm : 1≤m) (hvv' : v≠v')
    (p k pstar c t : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (hstar : 0≤pstar) (hstar1 : pstar≤1) (hplo : pstar≤p) (hklo : pstar≤k) (ht : 0<t)
    (hmany : c*(Fintype.card V:ℝ)^(m+1)≤Fintype.card (DenseRootMarkedPathFamily P π b m j T₀ TK v v')) :
    (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
      (fun σ=>markedPathSurvivalSum P π b m j T₀ TK v v' σ≤pstar^(m+4)*c-t)≤
      2*Real.exp (-2*t^2/(2*((m:ℝ)+1)*((m:ℝ)+4)/Fintype.card V)) := by
  let w := 1/(Fintype.card V:ℝ)^(m+1)
  let μ := markedPhysicalLaw p k hp hk hsum
  have hprod (C : DenseRootMarkedPathFamily P π b m j T₀ TK v v') :
      pstar^(m+4)≤∏ e∈markedPathRequiredEdges P π b m j T₀ TK v v' C,
        μ.mass (markedPathRequiredState P π b m j T₀ TK v v' C e) :=
    pattern_survival_product_lower _ _ pstar hstar hstar1
      (markedPathRequiredState_mass_lower P π b m j T₀ TK v v' hb hm hvv' p k pstar hp hk hsum hplo hklo C)
      (m+4) (markedPathRequiredEdges_card P π b m j T₀ TK v v' hb hm hvv' C).le
  have htotal : c≤∑ _ : DenseRootMarkedPathFamily P π b m j T₀ TK v v',w := by
    simp only [w,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one_div]
    exact (le_div_iff₀ (by positivity)).mpr hmany
  have hmean : pstar^(m+4)*c≤∑ C : DenseRootMarkedPathFamily P π b m j T₀ TK v v',
      w*∏ e∈markedPathRequiredEdges P π b m j T₀ TK v v' C,
        μ.mass (markedPathRequiredState P π b m j T₀ TK v v' C e) := by
    apply (mul_le_mul_of_nonneg_left htotal (pow_nonneg hstar _)).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro C _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hprod C) (show 0≤w by dsimp [w];positivity)
  apply le_trans _ (markedPathSurvivalSum_tail P π b m j T₀ TK v v' hn hb hm hvv' (fun _=>μ) t ht)
  apply finiteLaw_probability_mono
  intro σ hσ
  have hh := neg_le_abs (markedPathSurvivalSum P π b m j T₀ TK v v' σ-
    ∑ C : DenseRootMarkedPathFamily P π b m j T₀ TK v v',w*∏ e∈markedPathRequiredEdges P π b m j T₀ TK v v' C,
      μ.mass (markedPathRequiredState P π b m j T₀ TK v v' C e))
  change t≤|markedPathSurvivalSum P π b m j T₀ TK v v' σ-
    ∑ C : DenseRootMarkedPathFamily P π b m j T₀ TK v v',w*∏ e∈markedPathRequiredEdges P π b m j T₀ TK v v' C,
      μ.mass (markedPathRequiredState P π b m j T₀ TK v v' C e)|
  linarith only [hh,hmean,hσ]

end Oberwolfach
