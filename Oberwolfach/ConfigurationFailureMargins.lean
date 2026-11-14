module

public import Oberwolfach.AsymptoticMargins
public import Oberwolfach.RandomColourCuts

@[expose] public section

/-! Numerical margins for common configuration events. Constants and the order
threshold are chosen before the host, sample marginals, or root-index sets. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem linear_deviation_failure_eventually_small (C A ε : ℝ)
    (hA : 0<A) (hε : 0<ε) (K q : ℕ) :
    ∃ N : ℕ,∀ n : ℕ,N≤n → ∀ M D : ℝ,0≤M → M≤C*(n:ℝ)^K →
      0<D → D≤A*n →
      M*(2*Real.exp (-2*(ε*n)^2/D))≤1/(n:ℝ)^q := by
  obtain ⟨N,hN⟩ := eventually_stretchedExp_le_inv_pow (2*C) K
    (c:=2*ε^2/A) (p:=1) (by positivity) (by norm_num) q
  refine ⟨max N 1,?_⟩
  intro n hn M D hM hMb hD hDb
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hex : -2*(ε*n)^2/D≤-(2*ε^2/A)*n := by
    apply (div_le_iff₀ hD).mpr
    have hmul := mul_le_mul_of_nonneg_left hDb (by positivity : 0≤2*ε^2/A*n)
    have heq : (2*ε^2/A*n)*(A*n)=2*(ε*n)^2 := by field_simp <;> ring
    rw [heq] at hmul
    nlinarith only [hmul]
  calc
    _ ≤ M*(2*Real.exp (-(2*ε^2/A)*n)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) (by norm_num)) hM
    _ ≤ (C*(n:ℝ)^K)*(2*Real.exp (-(2*ε^2/A)*n)) :=
      mul_le_mul_of_nonneg_right hMb (by positivity)
    _ = (2*C)*(n:ℝ)^K*Real.exp (-(2*ε^2/A)*n) := by ring
    _ ≤ _ := by simpa only [Real.rpow_natCast,Real.rpow_one] using hN n (by omega)

theorem constant_deviation_failure_eventually_small (C A t : ℝ)
    (hA : 0<A) (ht : 0<t) (K q : ℕ) :
    ∃ N : ℕ,∀ n : ℕ,N≤n → ∀ M : ℝ,0≤M → M≤C*(n:ℝ)^K →
      M*(2*Real.exp (-2*t^2/(A/n)))≤1/(n:ℝ)^q := by
  obtain ⟨N,hN⟩ := eventually_stretchedExp_le_inv_pow (2*C) K
    (c:=2*t^2/A) (p:=1) (by positivity) (by norm_num) q
  refine ⟨max N 1,?_⟩
  intro n hn M hM hMb
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hex : -2*t^2/(A/n)=-(2*t^2/A)*n := by field_simp <;> ring
  rw [hex]
  calc
    _ ≤ (C*(n:ℝ)^K)*(2*Real.exp (-(2*t^2/A)*n)) :=
      mul_le_mul_of_nonneg_right hMb (by positivity)
    _ = (2*C)*(n:ℝ)^K*Real.exp (-(2*t^2/A)*n) := by ring
    _ ≤ _ := by simpa only [Real.rpow_natCast,Real.rpow_one] using hN n (by omega)

theorem paired_root_domain_card {V U : Type*} [Fintype V] [Fintype U]
    (hu : Fintype.card U≤Fintype.card V) (P : U×U → Prop) :
    Fintype.card (V×{a : U×U // P a})≤(Fintype.card V)^3 := by
  classical
  rw [Fintype.card_prod]
  have hs := Fintype.card_subtype_le P
  rw [Fintype.card_prod] at hs
  have hmul := Nat.mul_le_mul hu hu
  calc
    _ ≤ Fintype.card V*(Fintype.card V*Fintype.card V) := Nat.mul_le_mul_left _ (hs.trans hmul)
    _ = _ := by ring

theorem pair_neighbour_test_card {V U : Type*} [Fintype V] [Fintype U]
    (hu : Fintype.card U≤Fintype.card V) (hn : 0<Fintype.card V)
    (P : U×U → Prop) :
    (Fintype.card {a : U×U // P a}:ℝ)*(Fintype.card V+1)≤2*(Fintype.card V:ℝ)^3 := by
  classical
  have hs := Fintype.card_subtype_le P
  rw [Fintype.card_prod] at hs
  have hmul := Nat.mul_le_mul hu hu
  have hb : (Fintype.card {a : U×U // P a}:ℝ)≤(Fintype.card V:ℝ)^2 := by
    have hh : Fintype.card {a : U×U // P a}≤(Fintype.card V)^2 := by simpa only [pow_two] using hs.trans hmul
    exact_mod_cast hh
  have hn1 : (1:ℝ)≤Fintype.card V := by exact_mod_cast hn
  calc
    _ ≤ (Fintype.card V:ℝ)^2*(Fintype.card V+1) := mul_le_mul_of_nonneg_right hb (by positivity)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (show (Fintype.card V:ℝ)+1≤2*Fintype.card V by linarith) (sq_nonneg (Fintype.card V:ℝ))
      nlinarith only [hh]

theorem scaled_inverse_power_le (n q : ℕ) (hn : 0<n) (C : ℝ) (hC : C≤n) :
    C/(n:ℝ)^(q+1)≤1/(n:ℝ)^q := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  rw [pow_succ]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hn0 _) hn0) (pow_pos hn0 _)).mpr
  simpa only [one_mul,mul_one,mul_comm] using mul_le_mul_of_nonneg_right hC (pow_nonneg hn0.le q)

end Oberwolfach
