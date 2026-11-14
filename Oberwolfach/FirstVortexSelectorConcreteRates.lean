module

public import Oberwolfach.FirstVortexCommonHostMarginChoice
public import Oberwolfach.FirstVortexSeedDensityHierarchy

@[expose] public section
/-! Concrete host, boundary and seed parameters for the common selector,
with the host margin shared by the actual reference and matching inputs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_selector_concrete_rates
    (r d:ℕ) (αRef αMatch ε ρ₀ θ:ℝ)
    (hRef:0<αRef) (hMatch:0<αMatch)
    (hεRef:ε≤(2*αRef)/100000) (hεMatch:ε≤(2*αMatch)/100000)
    (hρ:0<ρ₀) (hρone:ρ₀≤1) (hθ:0<θ) (hspacing:1/(d:ℝ)≤θ/1024):
    let tstar:ℝ:=1/(200*((r+4:ℕ):ℝ))
    let kstar:ℝ:=ρ₀/(800*((r+4:ℕ):ℝ));
    ∃αHost cBoundary pstarRef:ℝ,
      0<αHost ∧ αHost≤2*αRef ∧ αHost≤2*αMatch ∧ ε≤αHost/100000 ∧
      (∀n:ℕ,∀D:ℝ,(1/2+2*αRef)*(n:ℝ)≤D→(1/2+αHost)*(n:ℝ)≤D) ∧
      cBoundary=θ ∧ 0<cBoundary ∧ 4/(d:ℝ)≤cBoundary ∧
      pstarRef=kstar ∧ 0<pstarRef ∧ 4*(((r+4):ℕ):ℝ)*pstarRef≤ρ₀*(1/100) ∧
      tstar≤(1/100)/(((r+4):ℕ):ℝ) ∧
      ∀ρ:ℝ,ρ₀≤ρ→ρ≤1→
        kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2 :=by
  intro tstar kstar
  obtain ⟨αHost,hHost,hHostRef,hHostMatch,hε,hMargin⟩:=
    first_vortex_common_host_margin_choice αRef αMatch ε hRef hMatch hεRef hεMatch
  obtain ⟨s,t,k,hs,ht,hk,hsp,hsCap,htp,ht1,hts,htBound,hkp,hkhalf,hpBound,hDensity⟩:=
    first_vortex_seed_density_hierarchy r ρ₀ hρ hρone
  have htstar:tstar=t:=by simpa only [tstar] using ht.symm
  have hkstar:kstar=k:=by simpa only [kstar] using hk.symm
  have hb:4/(d:ℝ)≤θ:=by
    have heq:4/(d:ℝ)=4*(1/(d:ℝ)):=by ring
    rw [heq]
    linarith
  refine ⟨αHost,θ,kstar,hHost,hHostRef,hHostMatch,hε,hMargin,rfl,hθ,hb,rfl,?_,?_,?_,?_⟩
  · simpa only [hkstar] using hkp
  · simpa only [hkstar] using hpBound
  · simpa only [htstar] using htBound
  · intro ρ hρlo hρhi
    obtain ⟨h₁,h₂,_,_,_,_,_,_,_,_⟩:=hDensity ρ t hρlo hρhi (le_refl t)
    constructor
    · simpa only [hs,hkstar] using h₁
    · rw [hkstar]
      rw [hs] at h₂
      convert h₂ using 1 <;> ring
end Oberwolfach
