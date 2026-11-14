module

public import Oberwolfach.MatchingGaussianBounds
public import Oberwolfach.MatchingPowerScales
public import Oberwolfach.MatchingCommonBounds

@[expose] public section

/-! Weighted matching with one explicit, polynomial-times-exponential failure
margin. All constants and the colour threshold are fixed before the graph,
weight functions and partition order. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem weighted_matching_large_scales (k : ℕ) (hk : 2≤k)
    (η K a : ℝ) (hη : 0<η) (hη1 : η≤1/100) (hK : 0<K) (ha : 0<a) :
    ∃ c : ℝ,0<c ∧ ∃ H : ℕ,2≤H ∧
    ∀ h n D J : ℕ,H≤h → h^(64*k)≤n → n≤D → D≤h^J →
    10*(h : ℝ)^(16+3*J)*Real.exp (-c*h)<1 →
    ∀ (V E A : Type) [Fintype V] [Fintype E] [Fintype A] [DecidableEq V],
    ∀ (R : E → Finset V) (w : A → E → ℝ) (b W : A → ℝ),
    Fintype.card V≤h^J → Fintype.card A≤h^J →
    (∀ e,(R e).card=k) → (∀ v,0<Fintype.card (HypergraphEdgesAt R v)) →
    (∀ v,Fintype.card (HypergraphEdgesAt R v)≤D) →
    (∀ v z,v≠z → ((Finset.univ.filter (fun e=>v∈R e ∧ z∈R e)).card : ℝ)≤K*D/n) →
    (∀ i,0<b i) → (∀ i e,0≤w i e ∧ w i e≤b i) →
    (∀ i,∑ e,w i e=W i) → (∀ i,a*b i*D*n≤W i) →
    ∃ M : Finset E,(∀ e∈M,∀ f∈M,e≠f → Disjoint (R e) (R f)) ∧
      ∀ i,|(∑ e∈M,w i e)-W i/D|<10*η*W i/D := by
  obtain ⟨N,hN⟩ := finite_weighted_hypergraph_matching k hk η (1/2) hη (by linarith) (by norm_num) (by norm_num)
  let c := min (2*η^2/(K*k)) (min (2*η^2*a/k) (min (η^2/8) (min (1/2) (a/8))))
  have hkR : (1 : ℝ)<k := by exact_mod_cast hk
  have hc : 0<c := by dsimp [c];repeat' apply lt_min <;> positivity
  have hc₀ : c≤2*η^2/(K*k) := min_le_left _ _
  have hc₁ : c≤2*η^2*a/k := (min_le_right _ _).trans (min_le_left _ _)
  have hc₂ : c≤η^2/8 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc₃ : c≤1/2 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hc₄ : c≤a/8 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let H := max (max (max 2 N) ⌈2*K⌉₊) ⌈1/η⌉₊
  have hH2 : 2≤H := by dsimp [H];omega
  refine ⟨c,hc,H,hH2,?_⟩
  intro h n D J hH hn hDn hDJ hsmall V E A _ _ _ _ R w b W hV hA hsize hpositive hdegree hcodeg hb hw htotal hweight
  have hh : 2≤h := hH2.trans hH
  have hh0 : 0<h := by omega
  have hhR : (1 : ℝ)≤h := by exact_mod_cast (show 1≤h by omega)
  have hn0 : 0<n := lt_of_lt_of_le (pow_pos hh0 _) hn
  have hD0 : 0<D := hn0.trans_le hDn
  have hnR : (0 : ℝ)<n := Nat.cast_pos.mpr hn0
  have hDR : (0 : ℝ)<D := Nat.cast_pos.mpr hD0
  have hKh : 2*K≤h := by
    have hh' : ⌈2*K⌉₊≤h := by dsimp [H] at hH;omega
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hh')
  have hηh : 1≤η*(h : ℝ)^4 := by
    have hh' : ⌈1/η⌉₊≤h := by dsimp [H] at hH;omega
    have he : 1/η≤(h : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hh')
    have hm := (div_le_iff₀ hη).mp he
    have hp : (h : ℝ)≤(h : ℝ)^4 := by simpa only [pow_one] using pow_le_pow_right₀ hhR (by norm_num : 1≤4)
    nlinarith [mul_le_mul_of_nonneg_left hp hη.le]
  let p := h^16
  let q := D/h^(16*k-12)
  let d := ⌈(1+4*η)*(h : ℝ)^4⌉₊
  let l := ⌈(1+η)*(d : ℝ)⌉₊
  have hbase : h^(16*k)≤D :=
    (Nat.pow_le_pow_right (by omega) (by omega : 16*k≤64*k)).trans (hn.trans hDn)
  obtain ⟨hq,hqD,hd,hl₀,hl₁,hDl,hlD,hmean⟩ := matching_edge_split_scale k h D hk hh η hη hη1 hηh hbase
  change 0<q at hq
  change q≤D at hqD
  change h^4≤d at hd
  change (D : ℝ)≤(p : ℝ)^(k-1)*q*l at hDl
  change (p : ℝ)^(k-1)*q*l≤(1+8*η)*D at hlD
  change (1+η)*(D : ℝ)/((p : ℝ)^(k-1)*q)≤(1+3*η)*(h : ℝ)^4 at hmean
  have hp : 0<p := pow_pos hh0 _
  have hpR : (0 : ℝ)<p := Nat.cast_pos.mpr hp
  have hqR : (0 : ℝ)<q := Nat.cast_pos.mpr hq
  have hp1 : (1 : ℝ)≤p := by exact_mod_cast hp
  have hdN : N≤d := by
    have hNh : N≤h := by dsimp [H] at hH;omega
    have hp4 : h≤h^4 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<h) (by norm_num : 1≤4)
    exact hNh.trans (hp4.trans hd)
  have hcodeSmall : (h : ℝ)≤(d : ℝ)^(1-(1/2 : ℝ)) := by
    rw [show 1-(1/2 : ℝ)=1/2 by norm_num,← Real.sqrt_eq_rpow]
    apply Real.le_sqrt_of_sq_le
    have he : (h : ℝ)^4≤d := by exact_mod_cast hd
    exact (pow_le_pow_right₀ hhR (by norm_num : 2≤4)).trans he
  obtain ⟨hs0,hs1,hs2,hs3⟩ := matching_power_scales k h D n hk hh hDn hn K hK hKh
  have hpCast : (p : ℝ)=(h : ℝ)^16 := by dsimp [p];push_cast;rfl
  rw [← hpCast] at hs0 hs1 hs2
  change (h : ℝ)*(p : ℝ)^k*q≤(D : ℝ)*n at hs1
  change (D : ℝ)^2*(p : ℝ)*h≤4*((p : ℝ)^k)^2*q^2 at hs2
  change (K*D/n)/(q : ℝ)≤1 at hs3
  have hW : ∀ i,0<W i := fun i=>(mul_pos (mul_pos (mul_pos ha (hb i)) hDR) hnR).trans_le (hweight i)
  have hL : ∀ i v,hypergraphWeightedDegree R (w i) v≤b i*D := by
    intro i v
    unfold hypergraphWeightedDegree
    calc
      _ ≤ ∑ e : E,if v∈R e then b i else 0 := by apply Finset.sum_le_sum;intro e _;split_ifs <;> simp_all only [le_refl,hw]
      _ = b i*Fintype.card (HypergraphEdgesAt R v) := by
        rw [← Finset.sum_filter,Finset.sum_const]
        simp only [nsmul_eq_mul,HypergraphEdgesAt,Fintype.card_subtype]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hdegree v)) (hb i).le
  have hsroot : (h : ℝ)*((p : ℝ)^(k-1))^2≤n := by
    calc
      _ = (h : ℝ)*(p : ℝ)^(2*(k-1)) := by rw [← pow_mul];congr 2;omega
      _ ≤ (h : ℝ)*(p : ℝ)^(2*k) := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp1 (by omega)) (by positivity)
      _ ≤ _ := hs0
  have hsweight : (h : ℝ)*((p : ℝ)^k)^2≤n := by simpa only [← pow_mul,Nat.mul_comm k 2] using hs0
  letI : NeZero p := ⟨by omega⟩
  letI : NeZero q := ⟨by omega⟩
  let f₀ := fun v : V=>-2*(η*D/(p : ℝ)^(k-1))^2/((K*D/n)*((k : ℝ)-1)*Fintype.card (HypergraphEdgesAt R v))
  let f₁ := fun i : A=>-2*(η*W i/(p : ℝ)^k)^2/(b i*D*k*W i)
  let f₂ := ((D : ℝ)/(p : ℝ)^(k-1)+η*D/(p : ℝ)^(k-1))/q*(Real.exp (η/4)-1)-(η/4)*((d : ℝ)+1)
  let f₃ := (K*D/n)/(q : ℝ)*(Real.exp 1-1)-((h : ℝ)+1)
  let f₄ := fun i : A=>(((W i/(p : ℝ)^k+η*W i/(p : ℝ)^k)/q*(Real.exp (1/4)-1)-(1/4)*(2*W i/((p : ℝ)^k*q)))/b i)
  let f₅ := fun i : A=>-2*(η*W i/D)^2/((p : ℝ)*(2*W i/((p : ℝ)^k*q))^2)
  have hf₀ : ∀ v,f₀ v≤-c*h := by
    intro v
    exact (matching_root_exponent hη hDR (by positivity) hK hkR hnR (by positivity)
      (Nat.cast_pos.mpr (hpositive v)) (Nat.cast_le.mpr (hdegree v)) hsroot).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hc₀ (show (0 : ℝ)≤h by positivity)])
  have hf₁ : ∀ i,f₁ i≤-c*h := by
    intro i
    exact (matching_vertex_weight_exponent hη (hW i) (by positivity) (hb i) hDR (by linarith) ha
      (by positivity) hsweight (hweight i)).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hc₁ (show (0 : ℝ)≤h by positivity)])
  have hf₂ : f₂≤-c*h := by
    have hm : ((D : ℝ)/(p : ℝ)^(k-1)+η*D/(p : ℝ)^(k-1))/q≤(1+3*η)*(h : ℝ)^4 := by
      convert hmean using 1 <;> field_simp <;> ring
    have he := matching_degree_exponent hη hη1 (show (0 : ℝ)≤h by positivity) hm (Nat.le_ceil _)
    change f₂≤_ at he
    have hp4 : (h : ℝ)≤(h : ℝ)^4 := by simpa only [pow_one] using pow_le_pow_right₀ hhR (by norm_num : 1≤4)
    have hc' := mul_le_mul_of_nonneg_right hc₂ (show (0 : ℝ)≤h by positivity)
    have he' := mul_le_mul_of_nonneg_left hp4 (show 0≤η^2/8 by positivity)
    exact he.trans (by nlinarith)
  have hf₃ : f₃≤-c*h :=
    (matching_codegree_exponent (by exact_mod_cast hh) hs3).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hc₃ (show (0 : ℝ)≤h by positivity)])
  have hf₄ : ∀ i,f₄ i≤-c*h := by
    intro i
    exact (matching_edge_weight_exponent hη.le hη1 (hW i) (by positivity) hqR (hb i) hDR ha
      (by positivity) hs1 (hweight i)).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hc₄ (show (0 : ℝ)≤h by positivity)])
  have hf₅ : ∀ i,f₅ i≤-c*h := by
    intro i
    exact (matching_selected_weight_exponent hη (hW i) hDR (by positivity) hpR hqR (by positivity) hs2).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hc₂ (show (0 : ℝ)≤h by positivity)])
  obtain ⟨hvEvent,heEvent,hsEvent⟩ := matching_failure_sums V (Fin p) (Fin q) A ((h : ℝ)^J) (-c*h)
    (one_le_pow₀ hhR) (by exact_mod_cast hV) (by simp only [Fintype.card_fin];exact_mod_cast hqD.trans hDJ)
    (by exact_mod_cast hA) f₀ f₁ f₄ f₅ f₂ f₃ hf₀ hf₁ hf₂ hf₃ hf₄ hf₅
    (by
      simpa only [Fintype.card_fin,hpCast,← pow_mul,← pow_add,Nat.mul_comm J 3,mul_assoc] using hsmall)
  obtain ⟨M,hM,hMw⟩ := hN d h hdN hcodeSmall V E (Fin p) (Fin q) A R w b W
    (fun i=>b i*D) (fun i=>η*W i/(p : ℝ)^k) (fun i=>2*W i/((p : ℝ)^k*q)) (fun i=>η*W i/D)
    D (K*D/n) (η*D/(p : ℝ)^(k-1)) (η/4) 1 (1/4) hsize hpositive
    (fun v=>Nat.cast_le.mpr (hdegree v)) hcodeg (by positivity) (by positivity) (by positivity)
    hb hw htotal hW hL (fun i=>by have hi := hW i;positivity) (fun i=>by have hi := hW i;positivity) (by positivity) (by norm_num) (by norm_num)
    (by simpa only [Fintype.card_fin,f₀,f₁] using hvEvent)
    (by simpa only [Fintype.card_fin,f₂,f₃,f₄,one_mul] using heEvent)
    (by simpa only [Fintype.card_fin,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,f₅] using hsEvent)
  refine ⟨M,hM,fun i=>?_⟩
  apply matching_normalization_error (hW i).le hDR hη.le hDl hlD
  have hlR : (0 : ℝ)<l := by dsimp [l];exact Nat.cast_pos.mpr (Nat.ceil_pos.mpr (by positivity))
  have hi := hMw i
  simp only [Fintype.card_fin] at hi
  change |(∑ e∈M,w i e)-W i/((p : ℝ)^(k-1)*q*l)|<
    η*W i/D+(p : ℝ)*(η*W i/(p : ℝ)^k)/(q*l) at hi
  have heq : (p : ℝ)*(η*W i/(p : ℝ)^k)/(q*l)=η*W i/((p : ℝ)^(k-1)*q*l) := by
    rw [show k=(k-1)+1 by omega,pow_succ]
    simp only [Nat.add_sub_cancel]
    field_simp
  rw [heq] at hi
  exact hi

end Oberwolfach
