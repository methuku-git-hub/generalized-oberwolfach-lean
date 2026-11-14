module

public import Oberwolfach.OrdinarySeedLift

@[expose] public section

/-! The degree-normalized original cycle weights meet the coefficient
scale needed for the fixed-seed concentration theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_degree_normalized_seed_bounds {V:Type} [Fintype V] [DecidableEq V]
    (P F:SimpleGraph V) (r:ℕ) (hr:2≤r) (hn:0<Fintype.card V)
    (weight:OrdinaryCycle P r→ℝ) (hweight:∀ C,0≤weight C)
    (B:ℝ) (hB:0≤B) (hb:∀ C,weight C≤B/(Fintype.card V:ℝ)^(r-2))
    (D:ℝ) (hD:(Fintype.card V:ℝ)/2≤D):
    ∀ W:OrdinaryWheel P F (fun (_:V) (_:Unit)=>True) r,
      0≤ordinaryCycleWheelWeight P F r weight (D/2) W ∧
      ordinaryCycleWheelWeight P F r weight (D/2) W≤(4*B)/(Fintype.card V:ℝ)^(r-1) := by
  intro W
  have hn0:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hD0:0<D/2:=by linarith
  have hDquarter:(Fintype.card V:ℝ)/4≤D/2:=by linarith
  have hinv:1/(D/2)≤4/(Fintype.card V:ℝ):=by
    apply (div_le_div_iff₀ hD0 hn0).mpr
    linarith only [hDquarter]
  have hw:=hb W.val.1
  have hpow:0<(Fintype.card V:ℝ)^(r-2):=by positivity
  have hscale:weight W.val.1*(1/(D/2))≤(B/(Fintype.card V:ℝ)^(r-2))*(4/(Fintype.card V:ℝ)):=
    mul_le_mul hw hinv (by positivity) (div_nonneg hB hpow.le)
  have heq:(B/(Fintype.card V:ℝ)^(r-2))*(4/(Fintype.card V:ℝ))=
      (4*B)/(Fintype.card V:ℝ)^(r-1):=by
    have hsub:(r-2)+1=r-1:=by omega
    rw [←hsub,pow_succ]
    field_simp
  refine ⟨?_,?_⟩
  · exact div_nonneg (hweight W.val.1) hD0.le
  · change weight W.val.1/(D/2)≤_
    rw [div_eq_mul_inv,←one_div]
    exact hscale.trans_eq heq
end Oberwolfach
