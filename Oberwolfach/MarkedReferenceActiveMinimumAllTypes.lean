module

public import Oberwolfach.MarkedReferenceLevelData

@[expose] public section
/-! A threshold chosen after the event's minimum size, but before the level
objects, makes both fixed active domains large enough. -/
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

theorem marked_active_minimum_threshold
    (θ iota omega:ℝ) (hθ:θ<1) (hiota:0 < iota) (homega:0 < omega) (M:ℕ):
    ∃ N₀:ℕ,∀ (n:ℕ) (a b:ℝ),N₀≤n→iota*n≤a→ omega*a≤b →
      (M:ℝ)≤(1-θ)*a ∧ (M:ℝ)≤(1-θ)*b:=by
  let cI:ℝ:=(1-θ)*iota
  let cJ:ℝ:=(1-θ)*omega*iota
  have hI:0<cI:=by dsimp [cI]; positivity
  have hJ:0<cJ:=by dsimp [cJ]; positivity
  let c:=min cI cJ
  have hc:0<c:=lt_min hI hJ
  obtain ⟨N₀,hN⟩:=exists_nat_gt ((M:ℝ)/c)
  refine ⟨N₀,?_⟩
  intro n a b hn hbase hJbase
  have hn':(N₀:ℝ)≤n:=by exact_mod_cast hn
  have hm:(M:ℝ)≤c*(n:ℝ):=by
    have hh:((M:ℝ)/c)<(n:ℝ):=hN.trans_le hn'
    have hh':(M:ℝ)<(n:ℝ)*c:=(div_lt_iff₀ hc).1 hh
    nlinarith
  have hcard:0≤(n:ℝ):=Nat.cast_nonneg _
  have hmI:(M:ℝ)≤cI*(n:ℝ):=hm.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hcard)
  have hmJ:(M:ℝ)≤cJ*(n:ℝ):=hm.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hcard)
  have hθ0:0≤1-θ:=by linarith
  have hIbound:=mul_le_mul_of_nonneg_left hbase hθ0
  have hJbound:=mul_le_mul_of_nonneg_left hJbase hθ0
  have hIomega:=mul_le_mul_of_nonneg_left hbase (mul_nonneg hθ0 (le_of_lt homega))
  constructor
  · dsimp [cI] at hmI
    nlinarith
  · dsimp [cJ] at hmJ
    nlinarith

theorem marked_reference_active_minimum_uniform_all_types
    (θ:ℝ) (hθ:θ<1) (hiota:0 < iota) (homega:0 < omegaI) (M:ℕ):
    ∃ N₀:ℕ,∀ (Gamma Color:Type) [Fintype Gamma] [Fintype Color]
      (level:MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal),
    letI:Fintype level.VP:=level.inst7
    N₀≤Fintype.card level.VP →
    (M:ℝ)≤(1-θ)*((level.I).card:ℝ) ∧
    (M:ℝ)≤(1-θ)*((level.J).card:ℝ):=by
  obtain ⟨N₀,hN⟩:=marked_active_minimum_threshold θ iota omegaI hθ hiota homega M
  refine ⟨N₀,?_⟩
  intro Gamma Color _ _ level hn
  letI:Fintype level.VP:=level.inst7
  exact hN (Fintype.card level.VP) level.I.card level.J.card hn level.hIotaSize level.hJlow
end Oberwolfach
