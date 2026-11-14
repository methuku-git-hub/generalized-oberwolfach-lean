module

public import Oberwolfach.OrdinaryFullHostLoadEvent
public import Oberwolfach.AsymptoticMargins
public import Oberwolfach.RandomColourCuts

@[expose] public section

/-! Uniform order thresholds for the full-host load event. The threshold
may depend on the fixed interval parameter, but not on the host or the
individual cycle coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
namespace Oberwolfach

theorem ordinary_resource_domain_card {V U : Type*} [Fintype V] [Fintype U]
    (hu : Fintype.card U≤Fintype.card V) :
    Fintype.card (Sym2 V⊕(V×U))≤2*(Fintype.card V)^2 := by
  rw [Fintype.card_sum,Fintype.card_prod]
  have hs := card_unorderedPairs_le_square (V:=V)
  have hm := Nat.mul_le_mul_left (Fintype.card V) hu
  nlinarith

theorem ordinary_load_failure_eventually_small (r d q : ℕ) (hr : 2≤r)
    (B t : ℝ) (hB : 0<B) (ht : 0<t) :
    ∃ N : ℕ,∀ n : ℕ,N≤n → ∀ M : ℝ,0≤M → M≤2*(n:ℝ)^2 →
      M*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((r:ℝ)^4*B/n)*(2*r)*((r:ℝ)^2*B))))≤1/(n:ℝ)^q := by
  have hr0 : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  let A : ℝ := (4*(d:ℝ)+3)^2*((r:ℝ)^4*B)*(2*r)*((r:ℝ)^2*B)
  have hA : 0<A := by dsimp [A];positivity
  obtain ⟨N,hN⟩ := eventually_stretchedExp_le_inv_pow 4 2
    (c:=2*t^2/A) (p:=1) (by positivity) (by norm_num) q
  refine ⟨max N 1,?_⟩
  intro n hn M hM hMb
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hden : (4*(d:ℝ)+3)^2*((r:ℝ)^4*B/n)*(2*r)*((r:ℝ)^2*B)=A/n := by dsimp [A];ring
  have hex : -2*t^2/(A/n)=-(2*t^2/A)*(n:ℝ) := by field_simp <;> ring
  rw [hden,hex]
  calc
    _ ≤ (2*(n:ℝ)^2)*(2*Real.exp (-(2*t^2/A)*(n:ℝ))) :=
      mul_le_mul_of_nonneg_right hMb (by positivity)
    _ = 4*(n:ℝ)^2*Real.exp (-(2*t^2/A)*(n:ℝ)) := by ring
    _ ≤ _ := by simpa only [Real.rpow_two,Real.rpow_one] using hN n (by omega)

end Oberwolfach
