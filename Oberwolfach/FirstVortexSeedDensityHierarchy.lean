module

public import Oberwolfach.FirstVortexSeedDensityAlignment

@[expose] public section
/-! Fix the selector's seed constants before the host density and the
level-step density are chosen. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_seed_density_hierarchy
    (r:ℕ) (ρ₀:ℝ) (hρ₀:0<ρ₀) (hρ₀one:ρ₀≤1):
    ∃sstar tstar kstar:ℝ,
      sstar=1/100 ∧ tstar=1/(200*((r+4:ℕ):ℝ)) ∧ kstar=ρ₀/(800*((r+4:ℕ):ℝ)) ∧
      0<sstar ∧ sstar≤1/100 ∧ 0<tstar ∧ tstar≤1 ∧ tstar≤sstar ∧
      tstar≤(1/100)/(((r+4):ℕ):ℝ) ∧ 0<kstar ∧ kstar≤1/2 ∧
      4*(((r+4):ℕ):ℝ)*kstar≤ρ₀*(1/100) ∧
    ∀ρ t:ℝ,ρ₀≤ρ→ρ≤1→tstar≤t→
      let p:=ρ*sstar/2
      let kval:=p/(((r+4):ℕ):ℝ);
      kstar≤p ∧ kstar≤kval ∧ kstar≤sstar ∧ p≤1 ∧ kval≤1 ∧ sstar≤1 ∧
      ρ₀/400≤ρ*(((r+4):ℕ):ℝ)*t/2 ∧ kstar≤ρ*(((r+4):ℕ):ℝ)*t/2 ∧
      kstar≤ρ*t/2 ∧ kstar≤t :=by
  let sstar:ℝ:=1/100
  let tstar:ℝ:=1/(200*((r+4:ℕ):ℝ))
  let kstar:ℝ:=ρ₀/(800*((r+4:ℕ):ℝ))
  have htstar:0<tstar:=by dsimp [tstar];positivity
  have hBase:=first_vortex_seed_density_alignment r ρ₀ ρ₀ tstar hρ₀ le_rfl hρ₀one (by exact le_rfl)
  obtain ⟨hs,hs1,ht,ht1,hts,htm,hk,_,_,hpBound,_,_,hks,_,_,_,_,_,_,_⟩:=hBase
  have hkhalf:kstar≤1/2:=by linarith
  refine ⟨sstar,tstar,kstar,rfl,rfl,rfl,hs,hs1,ht,ht1,hts,htm,hk,hkhalf,hpBound,?_⟩
  intro ρ t hρlo hρhi htt p kval
  have hAll:=first_vortex_seed_density_alignment r ρ₀ ρ t hρ₀ hρlo hρhi (by simpa only [tstar] using htt)
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hkp,hkk,hks',hp1,hk1,hsone,hpA,hkm,hkt,hkt'⟩:=hAll
  exact ⟨hkp,hkk,hks',hp1,hk1,hsone,hpA,hkm,hkt,hkt'⟩
end Oberwolfach
