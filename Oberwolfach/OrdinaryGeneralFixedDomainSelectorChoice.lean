module

public import Oberwolfach.OrdinaryGeneralFixedDomainSelector

@[expose] public section
/-! Select the packaged triangle event at arbitrary positive sampling and
failure tolerances, with all constants fixed before the finite host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_fixed_domain_selector_choice
    (kmin m d:ℕ) (hm:3≤m) (hd:2≤d) (θ α pstar ω βP ηP row Lconf:ℝ)
    (hθ:cycleThreshold (m+1)≤θ) (hα:0<α) (hα1:α≤1) (hθ1:θ+α/2≤1)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω)
    (hβP:0<βP) (hβmax:βP≤(α/2)*pstar^2*pstar^2)
    (hβhub:βP≤ω*pstar^(m+7)/4) (hηP:0<ηP) (hrow:0<row) (hrowmax:row≤pstar^(m+7)/2) (hL:0≤Lconf):
    ∃(k:ℕ) (βH c B:ℝ),m+3≤k ∧ kmin≤k ∧ 0<βH ∧ 0<c ∧ 0<B ∧
    ∀ηH η χ:ℝ,0<ηH→0<η→η<1→0<χ→
    ∃ε:ℝ,0<ε ∧ ∃M:ℕ,1≤M ∧
      OrdinaryGeneralFixedDomainSelector m k d M hm hd θ α pstar ω βP ηP row ηH βH c B ε η χ Lconf hpstar :=by
  obtain ⟨k,βH,c,B,hk,hkmin,hβH,hc,hB,hmain⟩:=ordinary_combined_general_fixed_domains
    kmin m d hm hd θ α pstar ω βP ηP row Lconf hθ hα hα1 hθ1 hpstar hpstar1 hω hβP hβmax hβhub hηP hrow hrowmax hL
  refine ⟨k,βH,c,B,hk,hkmin,hβH,hc,hB,?_⟩
  intro ηH η χ hηH hη hη1 hχ
  obtain ⟨ε,hε,M,hM,hselector⟩:=hmain ηH η χ hηH hη hη1 hχ
  exact ⟨ε,hε,M,hM,hselector⟩
end Oberwolfach
