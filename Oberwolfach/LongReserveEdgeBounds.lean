module

public import Oberwolfach.FiniteTransitionErrors
public import Oberwolfach.TransportMatrices

@[expose] public section

/-! The two alternatives in the reserve-edge estimate. The prefix and suffix
are actual transition products; the endpoint matrix has both specified marginals. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def reservedEdgeLoad {X V W Z : Type*} [Fintype X] [Fintype Z]
    (Q : X → Z → ℝ) (U : X → V → ℝ) (E : V → W → ℝ)
    (S : W → Z → ℝ) (T : X → Z → ℝ) (v : V) (w : W) : ℝ :=
  ∑ x, ∑ z, Q x z * U x v * E v w * S w z / T x z

theorem near_uniform_ratio_bound (a b p : ℝ) (hp : 0 < p)
    (ha : (9/10)*p ≤ a) (hb : b ≤ (11/10)*p) : b/a ≤ 11/9 := by
  have ha0 : 0 < a := by nlinarith
  apply (div_le_iff₀ ha0).mpr
  nlinarith

theorem reservedEdgeLoad_suffix_bound {X V W Z : Type*} [Fintype X] [Fintype Z]
    (Q : X → Z → ℝ) (U : X → V → ℝ) (E : V → W → ℝ)
    (S : W → Z → ℝ) (T : X → Z → ℝ)
    (d : X → ℝ) (d' : V → ℝ) (π : Z → ℝ)
    (hQ : ∀ x z, 0 ≤ Q x z) (hU : ∀ x v, 0 ≤ U x v) (hE : ∀ v w, 0 ≤ E v w)
    (hrow : ∀ x, ∑ z, Q x z = d x/3)
    (hprop : ∀ v, ∑ x, d x*U x v = d' v)
    (hπ : ∀ z, 0 < π z) (hT : ∀ x z, (9/10)*π z ≤ T x z)
    (hS : ∀ w z, S w z ≤ (11/10)*π z) (v : V) (w : W) :
    reservedEdgeLoad Q U E S T v w ≤ (11/27)*(d' v*E v w) := by
  unfold reservedEdgeLoad
  calc
    (∑ x, ∑ z, Q x z*U x v*E v w*S w z/T x z) ≤
        ∑ x, ∑ z, (Q x z*U x v*E v w)*(11/9) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro z _
      have hratio := near_uniform_ratio_bound (T x z) (S w z) (π z) (hπ z) (hT x z) (hS w z)
      have hh := mul_le_mul_of_nonneg_left hratio
        (mul_nonneg (mul_nonneg (hQ x z) (hU x v)) (hE v w))
      convert hh using 1 <;> ring
    _ = ∑ x, (d x*U x v)*(E v w*(11/27)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.sum_mul,hrow]
      ring
    _ = (11/27)*(d' v*E v w) := by rw [← Finset.sum_mul,hprop]; ring

theorem reservedEdgeLoad_prefix_bound {X V W Z : Type*} [Fintype X] [Fintype Z]
    (Q : X → Z → ℝ) (U : X → V → ℝ) (E : V → W → ℝ)
    (S : W → Z → ℝ) (T : X → Z → ℝ)
    (πV : V → ℝ) (πZ : Z → ℝ) (M : ℝ)
    (hQ : ∀ x z, 0 ≤ Q x z) (hE : ∀ v w, 0 ≤ E v w)
    (hS : IsTransition S) (hπV : ∀ v, 0 ≤ πV v) (hπZ : ∀ z, 0 < πZ z)
    (hcol : ∀ z, ∑ x, Q x z = M*πZ z/3)
    (hT : ∀ x z, (9/10)*πZ z ≤ T x z)
    (hU : ∀ x v, U x v ≤ (11/10)*πV v) (v : V) (w : W) :
    reservedEdgeLoad Q U E S T v w ≤ (11/27)*(M*πV v*E v w) := by
  have hratio (x : X) (z : Z) : U x v/T x z ≤ (11/9)*πV v/πZ z := by
    have hT0 : 0 < T x z := by nlinarith [hT x z,hπZ z]
    apply (div_le_iff₀ hT0).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (hπZ z)).mpr
    have h1 := mul_le_mul_of_nonneg_right (hU x v) (hπZ z).le
    have h2 := mul_le_mul_of_nonneg_left (hT x z) (hπV v)
    nlinarith
  unfold reservedEdgeLoad
  calc
    (∑ x, ∑ z, Q x z*U x v*E v w*S w z/T x z) ≤
        ∑ x, ∑ z, (Q x z*E v w*S w z)*((11/9)*πV v/πZ z) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro z _
      have hh := mul_le_mul_of_nonneg_left (hratio x z)
        (mul_nonneg (mul_nonneg (hQ x z) (hE v w)) (hS.1 w z))
      convert hh using 1 <;> ring
    _ = ∑ z, ((11/27)*(M*πV v*E v w))*S w z := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.sum_mul,hcol]
      field_simp [(hπZ z).ne']
      <;> ring
    _ = (11/27)*(M*πV v*E v w) := by rw [← Finset.mul_sum,hS.2,mul_one]

end Oberwolfach
