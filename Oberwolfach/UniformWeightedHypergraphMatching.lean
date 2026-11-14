module

public import Oberwolfach.WeightedMatchingLargeScales

@[expose] public section

/-! A self-contained fixed-error weighted matching theorem. The degree,
codegree and weight hypotheses are checked before sampling; one matching
satisfies every prescribed weight simultaneously. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem uniform_weighted_hypergraph_matching (k B : ℕ) (hk : 2≤k)
    (K a γ : ℝ) (hK : 0<K) (ha : 0<a) (hγ : 0<γ) :
    ∃ n₀ : ℕ, ∀ n D : ℕ,n₀≤n → n≤D → D≤n^B →
    ∀ (V E A : Type) [Fintype V] [Fintype E] [Fintype A] [DecidableEq V],
    ∀ (R : E → Finset V) (w : A → E → ℝ) (b W : A → ℝ),
    Fintype.card V≤n^B → Fintype.card A≤n^B →
    (∀ e,(R e).card=k) → (∀ v,0<Fintype.card (HypergraphEdgesAt R v)) →
    (∀ v,Fintype.card (HypergraphEdgesAt R v)≤D) →
    (∀ v z,v≠z → ((Finset.univ.filter (fun e=>v∈R e ∧ z∈R e)).card : ℝ)≤K*D/n) →
    (∀ i,0<b i) → (∀ i e,0≤w i e ∧ w i e≤b i) →
    (∀ i,∑ e,w i e=W i) → (∀ i,a*b i*D*n≤W i) →
    ∃ M : Finset E,(∀ e∈M,∀ f∈M,e≠f → Disjoint (R e) (R f)) ∧
      ∀ i,|(∑ e∈M,w i e)-W i/D|<γ*W i/D := by
  let η := min (γ/20) (1/100)
  have hη : 0<η := lt_min (by positivity) (by norm_num)
  have hη1 : η≤1/100 := min_le_right _ _
  have hηγ : 10*η≤γ := by have hh : η≤γ/20 := min_le_left _ _;linarith
  obtain ⟨c,hc,H₀,hH₀,hmatch⟩ := weighted_matching_large_scales k hk η K a hη hη1 hK ha
  let J := 128*k*B
  obtain ⟨N,hN⟩ := eventually_stretchedExp_le_inv_pow 10 ((16+3*J : ℕ) : ℝ) (c:=c) (p:=1) hc (by norm_num) 1
  let H := max H₀ N
  refine ⟨H^(64*k),?_⟩
  intro n D hn hDn hDB V E A _ _ _ _ R w b W hV hA hsize hpositive hdegree hcodeg hb hw htotal hweight
  obtain ⟨hH,hhpow,hnupper⟩ := matching_integer_root_scale (64*k) H n (by omega)
    (hH₀.trans (le_max_left _ _)) hn
  let h := Nat.nthRoot (64*k) n
  change H≤h at hH
  change h^(64*k)≤n at hhpow
  change n≤h^(2*(64*k)) at hnupper
  have hh : 2≤h := hH₀.trans ((le_max_left _ _).trans hH)
  have hhR : (1 : ℝ)<h := by exact_mod_cast hh
  have hnB : n^B≤h^J := by
    calc
      _ ≤ (h^(2*(64*k)))^B := Nat.pow_le_pow_left hnupper B
      _ = h^J := by rw [← pow_mul];congr 1;dsimp [J];ring
  have hsmall : 10*(h : ℝ)^(16+3*J)*Real.exp (-c*h)<1 := by
    have he := hN h ((le_max_right _ _).trans hH)
    simp only [Real.rpow_one,pow_one] at he
    have he' : 10*(h : ℝ)^(16+3*J)*Real.exp (-c*h)≤1/(h : ℝ) := by
      simpa only [Real.rpow_natCast] using he
    exact he'.trans_lt ((div_lt_one (by linarith : (0 : ℝ)<h)).mpr hhR)
  obtain ⟨M,hM,hMw⟩ := hmatch h n D J ((le_max_left _ _).trans hH) hhpow hDn
    (hDB.trans hnB) hsmall V E A R w b W (hV.trans hnB) (hA.trans hnB)
    hsize hpositive hdegree hcodeg hb hw htotal hweight
  refine ⟨M,hM,fun i=>(hMw i).trans_le ?_⟩
  have hn0 : 0<n := lt_of_lt_of_le (pow_pos (by omega : 0<h) _) hhpow
  have hD0 : 0<D := hn0.trans_le hDn
  have hW : 0<W i := (mul_pos (mul_pos (mul_pos ha (hb i)) (Nat.cast_pos.mpr hD0)) (Nat.cast_pos.mpr hn0)).trans_le (hweight i)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hηγ hW.le) (Nat.cast_nonneg _)

end Oberwolfach
