module

public import Oberwolfach.LongPreparationReferenceDensities

@[expose] public section
/-! Reference and approximate density floors fixed before the actual index
and physical densities are exposed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_reference_fixed_scales (m:ℕ) (hm:1≤m) (ρ₀:ℝ) (hρ₀:0<ρ₀):
    let sstar:ℝ:=1/100
    let tstar:ℝ:=sstar/(m:ℝ)
    let kstar:ℝ:=ρ₀*tstar/4
    let pstar:ℝ:=min sstar (min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((m:ℝ)+1)))));
    0<sstar ∧ sstar≤1/100 ∧ 0<tstar ∧ tstar≤1 ∧ tstar≤sstar ∧
    0<kstar ∧ kstar≤ρ₀*tstar/4 ∧ 0<pstar ∧ pstar≤sstar ∧
    ∀ ρ:ℝ,ρ₀≤ρ→
      let p:=ρ*sstar/2
      let k:=p/(m:ℝ);
      kstar≤p ∧ kstar≤k:=by
  intro sstar tstar kstar pstar
  have hs:0<sstar:=by dsimp [sstar];norm_num
  have hs1:sstar≤1:=by dsimp [sstar];norm_num
  have hmR:(0:ℝ)<m:=by exact_mod_cast (show 0<m by omega)
  have ht:0<tstar:=by dsimp [tstar];positivity
  have hts:tstar≤sstar:=by
    dsimp [tstar]
    exact div_le_self hs.le (by exact_mod_cast hm)
  have hk:0<kstar:=by dsimp [kstar];positivity
  have hp:0<pstar:=by dsimp [pstar];positivity
  refine ⟨hs,by dsimp [sstar];norm_num,ht,hts.trans hs1,hts,hk,le_rfl,hp,min_le_left _ _,?_⟩
  intro ρ hρ p k
  have hh:=long_preparation_reference_densities m hm ρ₀ ρ sstar hρ₀ hρ hs hs1
  exact ⟨hh.2.2.2.1,hh.2.2.2.2.1⟩
end Oberwolfach
