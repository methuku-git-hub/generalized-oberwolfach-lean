module

public import Oberwolfach.OrdinaryParentVortexSizeChoice

@[expose] public section
/-! One terminal scale accommodates the sampled-event and local-certificate
thresholds as well as the reciprocal-contraction requirement. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_unified_vortex_size_choice
    (ε:ℝ) (hε:0<ε) (v₀ m₀ Nmin Mhost Mcut:ℕ):
    ∃N mv:ℕ, Nmin≤N ∧ 2/ε≤(N:ℝ) ∧ 1≤mv ∧ v₀≤mv ∧ m₀≤mv ∧
      (N:ℝ)≤ε*mv/2 ∧ (Mhost:ℝ)≤ε*mv/2 ∧ (Mcut:ℝ)≤ε*mv/2 :=by
  obtain ⟨Nε,hNε⟩:=exists_nat_ge (2/ε)
  let N:=max Nmin Nε
  have hNmin:Nmin≤N:=le_max_left _ _
  have hNεN:Nε≤N:=le_max_right _ _
  have hNεR:(Nε:ℝ)≤N:=by exact_mod_cast hNεN
  obtain ⟨mv,hmv,hv₀,hm₀,hboth,hcut⟩:=ordinary_parent_vortex_size_choice ε hε v₀ m₀ (max Mhost N) Mcut
  have hN:(N:ℝ)≤(max Mhost N:ℕ):=by exact_mod_cast (le_max_right Mhost N)
  have hhost:(Mhost:ℝ)≤(max Mhost N:ℕ):=by exact_mod_cast (le_max_left Mhost N)
  exact ⟨N,mv,hNmin,hNε.trans hNεR,hmv,hv₀,hm₀,hN.trans hboth,hhost.trans hboth,hcut⟩
end Oberwolfach
