module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section
/-! Uniform degree margin throughout the deletion of the small factor classes. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem factor_small_removal_margin (D h n:ℕ) (δ α:ℝ)
    (hδ:0≤δ) (hα:0<α)
    (hdegree:(δ+α)*(n:ℝ)≤D) (hsmall:(h:ℝ)≤α*n/500):
    ∀ j≤h,2*j≤D ∧ (δ+α/2)*(n:ℝ)≤((D-2*j:ℕ):ℝ):=by
  intro j hj
  have hn:(0:ℝ)≤n:=by positivity
  have hjR:(j:ℝ)≤h:=by exact_mod_cast hj
  have hαn:0≤α*n:=mul_nonneg hα.le hn
  have hδn:0≤δ*n:=mul_nonneg hδ hn
  have hjbound:(2:ℝ)*j≤D:=by nlinarith
  have hjnat:2*j≤D:=by exact_mod_cast hjbound
  constructor
  · exact hjnat
  · rw [Nat.cast_sub hjnat]
    push_cast
    nlinarith

/-- The integer threshold used in the finite sequential-removal induction can
be fixed from the original degree margin. -/
theorem factor_small_removal_integer_margin (D h n:ℕ) (δ α:ℝ)
    (hδ:0≤δ) (hα:0<α)
    (hdegree:(δ+α)*(n:ℝ)≤D) (hsmall:(h:ℝ)≤α*n/500):
    ⌈(δ+α/2)*(n:ℝ)⌉₊+2*h≤D:=by
  obtain ⟨hsub,hreal⟩:=factor_small_removal_margin D h n δ α hδ hα hdegree hsmall h (le_refl h)
  have hceil:⌈(δ+α/2)*(n:ℝ)⌉₊≤D-2*h:=Nat.ceil_le.mpr hreal
  omega
end Oberwolfach
