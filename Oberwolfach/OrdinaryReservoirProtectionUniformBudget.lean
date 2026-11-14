module

public import Oberwolfach.OrdinaryReservoirAndProtectedCorrection

@[expose] public section
/-! A finite reservoir can be protected together with a sufficiently small
inner pair at every sufficiently large original host size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reservoir_protection_uniform_budget
    (ρ h:ℝ) (hρ:0<ρ) (hh:0<h):
    ∃ε₀ ζ:ℝ,0<ε₀ ∧ 0<ζ ∧ ζ≤h ∧
    ∀(f a b t:ℕ),∃N:ℕ,1≤N ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
      (Z:Finset V) (B:Finset U) (ε:ℝ),
      N≤Fintype.card V→ρ*Fintype.card V≤Fintype.card U→0≤ε→ε≤ε₀→
      (Z.card:ℝ)≤ε*Fintype.card V→(B.card:ℝ)≤ε*Fintype.card V+f→
      ((Z.card+2^(t*t)*a:ℕ):ℝ)≤ζ*Fintype.card V ∧
      ((B.card+2^(t*t)*b:ℕ):ℝ)≤ζ*Fintype.card U :=by
  let lam:ℝ:=min 1 ρ
  have hlam:0<lam:=lt_min (by norm_num) hρ
  have hlam1:lam≤1:=min_le_left _ _
  have hlamρ:lam≤ρ:=min_le_right _ _
  refine ⟨h*lam/8,h/2,by positivity,by positivity,by linarith,?_⟩
  intro f a b t
  let C:ℝ:=(f:ℝ)+(2^(t*t)*a:ℕ)+(2^(t*t)*b:ℕ)+1
  obtain ⟨N,hN⟩:=exists_nat_gt (4*C/(h*lam))
  refine ⟨max N 1,by omega,?_⟩
  intro V U _ _ _ _ Z B ε hn hUn hε hεsmall hZ hB
  have hnN:(N:ℝ)≤Fintype.card V:=by exact_mod_cast (show N≤Fintype.card V by omega)
  have hn0:(0:ℝ)≤Fintype.card V:=by positivity
  have hC:0≤C:=by dsimp [C];positivity
  have hcost:C≤(h*lam/4)*Fintype.card V:=by
    have hden:0<h*lam:=mul_pos hh hlam
    have hlarge:4*C/(h*lam)≤(Fintype.card V:ℝ):=hN.le.trans hnN
    have hmul:4*C≤(Fintype.card V:ℝ)*(h*lam):=(div_le_iff₀ hden).mp hlarge
    nlinarith only [hmul]
  have hlamn:(lam*(Fintype.card V:ℝ))≤Fintype.card U:=by
    exact (mul_le_mul_of_nonneg_right hlamρ hn0).trans hUn
  have hεn:ε*(Fintype.card V:ℝ)≤(h*lam/8)*Fintype.card V:=mul_le_mul_of_nonneg_right hεsmall hn0
  have ha:((2^(t*t)*a:ℕ):ℝ)≤C:=by
    dsimp [C]
    have hf:(0:ℝ)≤f:=by positivity
    have hb0:(0:ℝ)≤((2^(t*t)*b:ℕ):ℝ):=by positivity
    linarith
  have hb:(f:ℝ)+((2^(t*t)*b:ℕ):ℝ)≤C:=by
    dsimp [C]
    have ha0:(0:ℝ)≤((2^(t*t)*a:ℕ):ℝ):=by positivity
    linarith
  have hlamle:(h*lam)*(Fintype.card V:ℝ)≤h*Fintype.card V:=by
    have hh1:h*lam≤h:=by nlinarith only [hlam1,hh]
    exact mul_le_mul_of_nonneg_right hh1 hn0
  have hlamU:(h*lam)*(Fintype.card V:ℝ)≤h*Fintype.card U:=by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlamn hh.le
  push_cast at ha hb
  constructor <;> push_cast <;> nlinarith only [hZ,hB,hεn,hcost,ha,hb,hlamle,hlamU]
end Oberwolfach
