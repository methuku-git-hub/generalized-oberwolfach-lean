module

public import Oberwolfach.Vortex

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_host_first_matching_inputs
    {n D:ℕ} {U:Type} [Fintype U]
    (P:SimpleGraph (Fin n)) (ρ₀ ρ αRef γList:ℝ)
    (hreg:P.IsRegularOfDegree D) (hD:0<(D:ℝ))
    (hρlo:ρ₀≤ρ) (hρhi:ρ≤1) (hsize:ρ*D=2*Fintype.card U)
    (hDhi:(D:ℝ)≤2*n) (hmin:(1/2+αRef)*(n:ℝ)≤D)
    (hγ:γList≤αRef):
    0<D ∧ Fintype.card U≤n ∧ ρ₀/200≤ρ*(1/100)/2 ∧
    (∀v,(P.degree v:ℝ)=D) ∧ (∀v,(1/2+γList)*n≤(P.degree v:ℝ)):=by
  have hDn:0<D:=by exact_mod_cast hD
  have hDn0:0≤(D:ℝ):=hD.le
  have hmul:ρ*(D:ℝ)≤D:=by nlinarith [mul_nonneg (sub_nonneg.mpr hρhi) hDn0]
  have huR:(Fintype.card U:ℝ)≤n:=by nlinarith [hsize,hDhi]
  have hu:Fintype.card U≤n:=by exact_mod_cast huR
  have hγn:γList*(n:ℝ)≤αRef*n:=mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg n)
  refine ⟨hDn,hu,?_,?_,?_⟩
  · linarith
  · intro v; exact_mod_cast hreg v
  · intro v
    have hh:((P.degree v):ℝ)=D:=by exact_mod_cast hreg v
    rw [hh]
    nlinarith
end Oberwolfach
