module

public import Oberwolfach.MarkedReferenceLevelData

@[expose] public section
/-! The actual reference-level size hypotheses give the ambient-to-inner
comparisons required by the fixed-domain neighbourhood event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}

theorem marked_reference_active_ambient_bounds
    (level:MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (hiota:0 < iota) (homega:0 < omegaI):
    letI:Fintype level.VP:=level.inst7
    letI:Fintype level.UP:=level.inst8
    let K:=1+1/iota+1/(iota*omegaI)
    1≤K ∧ (Fintype.card level.VP:ℝ)≤K*level.I.card ∧
    (Fintype.card level.UP:ℝ)≤K*level.I.card ∧
    (Fintype.card level.VP:ℝ)≤K*level.J.card:=by
  intro K
  letI:Fintype level.VP:=level.inst7
  letI:Fintype level.UP:=level.inst8
  have hnI:(Fintype.card level.VP:ℝ)≤(1/iota)*(level.I.card:ℝ):=by
    rw [one_div,mul_comm]
    apply (le_div_iff₀ hiota).2
    simpa only [mul_comm] using level.hIotaSize
  have hnJ:(Fintype.card level.VP:ℝ)≤(1/(iota*omegaI))*(level.J.card:ℝ):=by
    have hprod:0 < iota*omegaI:=mul_pos hiota homega
    rw [one_div,mul_comm]
    apply (le_div_iff₀ hprod).2
    have hm:=mul_le_mul_of_nonneg_left level.hIotaSize (le_of_lt homega)
    nlinarith [level.hJlow]
  have hup:(Fintype.card level.UP:ℝ)≤Fintype.card level.VP:=by exact_mod_cast level.hUP
  have hK1:(1/iota:ℝ)≤K:=by
    dsimp [K]
    have hh:0≤(1/(iota*omegaI):ℝ):=by positivity
    linarith
  have hK2:(1/(iota*omegaI):ℝ)≤K:=by
    dsimp [K]
    have hh:0≤(1/iota:ℝ):=by positivity
    linarith
  have hI:0≤(level.I.card:ℝ):=Nat.cast_nonneg _
  have hJ:0≤(level.J.card:ℝ):=Nat.cast_nonneg _
  have hnI':(Fintype.card level.VP:ℝ)≤K*level.I.card:=
    hnI.trans (mul_le_mul_of_nonneg_right hK1 hI)
  have hK:1≤K:=by
    dsimp [K]
    have h1:0≤(1/iota:ℝ):=by positivity
    have h2:0≤(1/(iota*omegaI):ℝ):=by positivity
    linarith
  exact ⟨hK,hnI',hup.trans hnI',hnJ.trans (mul_le_mul_of_nonneg_right hK2 hJ)⟩
end Oberwolfach
