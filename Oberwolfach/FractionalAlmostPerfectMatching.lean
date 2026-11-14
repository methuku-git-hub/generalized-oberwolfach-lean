module

public import Oberwolfach.IndexedMatchingBridge

@[expose] public section

/-! A fractional almost-perfect matching theorem obtained by deterministic
rounding to indexed parallel copies and the checked Norin--Steiner iteration.
The explicit constant uses the formula in their Lean development. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem almost_perfect_matching_of_fractional_weights
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (R : E → Finset V) (r : ℕ) (hr : 2≤r) (hR : ∀ e, (R e).card=r)
    (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ≤1)
    (w : E → ℝ) (hw : ∀ e, 0≤w e)
    (hload : ∀ v, 1-HadwigerLean.Theorem2.matchingMu r ξ/4 ≤
      (∑ e, if v∈R e then w e else 0) ∧ (∑ e, if v∈R e then w e else 0)≤1)
    (hpair : ∀ u v, u≠v → (∑ e, if u∈R e ∧ v∈R e then w e else 0)≤
      HadwigerLean.Theorem2.matchingMu r ξ/4) :
    ∃ M : Finset E,
      (M : Set E).Pairwise (fun e f => Disjoint (R e) (R f)) ∧
      (1-ξ)*Fintype.card V ≤ ((M.biUnion R).card : ℝ) := by
  let μ := HadwigerLean.Theorem2.matchingMu r ξ
  have hμ : 0<μ := by
    dsimp [μ,HadwigerLean.Theorem2.matchingMu]
    have hrR : (0 : ℝ)<r := by exact_mod_cast (show 0<r by omega)
    positivity
  obtain ⟨T,hT⟩ := exists_nat_gt (4*((Fintype.card E : ℝ)+1)/μ)
  have hTbig : 4*((Fintype.card E : ℝ)+1)<μ*T := by
    have hh := (div_lt_iff₀ hμ).mp hT
    nlinarith
  have hTR : (0 : ℝ)<T := lt_of_lt_of_le
    (div_pos (by positivity) hμ) hT.le
  have hTN : 0<T := Nat.cast_pos.mp hTR
  let m (e : E) := ⌊(T : ℝ)*w e⌋₊
  let H := copiedResourceHypergraph R m
  let B := ⌈μ*T/2⌉₊
  have hBmin : 1≤B := by
    have hlow := Nat.le_ceil (μ*T/2)
    have he0 : (0 : ℝ)≤Fintype.card E := Nat.cast_nonneg _
    have hpos : (0 : ℝ)<B := by dsimp [B];linarith
    exact Nat.cast_pos.mp hpos
  have hBmax : (B : ℝ)≤μ*T := by
    have hb := Nat.ceil_lt_add_one (show 0≤μ*T/2 by positivity)
    have he0 : (0 : ℝ)≤Fintype.card E := Nat.cast_nonneg _
    dsimp [B];linarith
  have hcap (v : V) (_ : v∈H.vertices) : H.degree v≤T := by
    rw [copiedResource_degree]
    have hh := (sum_floor_scaled_weight_bounds w hw (fun e => v∈R e) T).2
    have hb := mul_le_mul_of_nonneg_left (hload v).2 hTR.le
    have hgoal : ((∑ e, if v∈R e then m e else 0 : ℕ) : ℝ)≤T := by
      exact hh.trans (by simpa only [mul_one] using hb)
    exact_mod_cast hgoal
  have hmin (v : V) (_ : v∈H.vertices) : (1-μ)*(T : ℝ)≤(H.degree v : ℝ) := by
    rw [copiedResource_degree]
    have hh := (sum_floor_scaled_weight_bounds w hw (fun e => v∈R e) T).1
    have hb := mul_le_mul_of_nonneg_left (hload v).1 hTR.le
    change (1-μ)*T≤((∑ e, if v∈R e then ⌊(T : ℝ)*w e⌋₊ else 0 : ℕ) : ℝ)
    change (T : ℝ)*(1-μ/4)≤_ at hb
    have he0 : (0 : ℝ)≤Fintype.card E := Nat.cast_nonneg _
    have hh' : (T : ℝ)*(∑ e, if v∈R e then w e else 0)-Fintype.card E ≤
        ((∑ e, if v∈R e then ⌊(T : ℝ)*w e⌋₊ else 0 : ℕ) : ℝ) := hh
    have hb' : (T : ℝ)*(1-μ/4)-Fintype.card E ≤
        ((∑ e, if v∈R e then ⌊(T : ℝ)*w e⌋₊ else 0 : ℕ) : ℝ) :=
      (sub_le_sub_right hb _).trans hh'
    exact (show (1-μ)*(T : ℝ)≤(T : ℝ)*(1-μ/4)-Fintype.card E by nlinarith).trans hb'
  have hcodeg (u v : V) (huv : u≠v) : H.codegree u v≤B := by
    rw [copiedResource_codegree]
    have hh := (sum_floor_scaled_weight_bounds w hw (fun e => u∈R e ∧ v∈R e) T).2
    have hb := mul_le_mul_of_nonneg_left (hpair u v huv) hTR.le
    have hceil := Nat.le_ceil (μ*T/2)
    have hgoal : ((∑ e, if u∈R e ∧ v∈R e then m e else 0 : ℕ) : ℝ)≤B := by
      change (T : ℝ)*(∑ e, if u∈R e ∧ v∈R e then w e else 0)≤(T : ℝ)*(μ/4) at hb
      change μ*T/2≤(B : ℝ) at hceil
      exact hh.trans (hb.trans ((show (T : ℝ)*(μ/4)≤μ*T/2 by
        nlinarith [mul_pos hμ hTR]).trans hceil))
    exact_mod_cast hgoal
  have hmax : H.maxCodegree≤B := by
    apply Finset.sup_le
    intro u _
    apply Finset.sup_le
    intro v hv
    exact hcodeg u v (Ne.symm (Finset.mem_erase.mp hv).1)
  obtain ⟨M,hM,hcovered⟩ := HadwigerLean.Theorem2.exists_almostPerfectMatching_of_degree_bounds H
    hr hξ hξ1 hTN hBmin hBmax (fun e _ => hR e.1) hcap hmin hmax
  obtain ⟨hproj,heq⟩ := copiedResource_matching_projection R m M hM
  refine ⟨M.image Sigma.fst,hproj,?_⟩
  rw [heq]
  simpa only [H,copiedResourceHypergraph,Finset.card_univ] using hcovered

end Oberwolfach
