module

public import Mathlib.Tactic

@[expose] public section
/-! The first five physical states have the original class density exactly. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem expanded_class_density_identity
    {U:Type} [Fintype U] (ρ D t s:ℝ) (a b:U→ℝ) (hD:D≠0)
    (hsize:ρ*D=2*Fintype.card U):
    2*(ρ*t/2)+2*(ρ*s/2)+2*(∑u,b u)/D+2*(∑u,a u)/D+
      2*(∑u,(1-t-s-a u-b u))/D=ρ:=by
  have hsum:(∑u,(1-t-s-a u-b u))=
      (Fintype.card U:ℝ)*(1-t-s)-(∑u,a u)-(∑u,b u):=by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ring
  have hcard:(Fintype.card U:ℝ)=ρ*D/2:=by linarith [hsize]
  rw [hsum,hcard]
  field_simp
  ring
end Oberwolfach
