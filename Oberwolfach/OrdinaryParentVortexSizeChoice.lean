module

public import Oberwolfach.OrdinaryExpandedVortexParentCommonWitness

@[expose] public section
/-! The terminal vortex scale can be chosen before n to accommodate both
parent-domain thresholds and any previously fixed lower bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_parent_vortex_size_choice
    (ε:ℝ) (hε:0<ε) (v₀ m₀ Mhost Mcut:ℕ):
    ∃mv:ℕ,1≤mv ∧ v₀≤mv ∧ m₀≤mv ∧
      (Mhost:ℝ)≤ε*mv/2 ∧ (Mcut:ℝ)≤ε*mv/2 :=by
  obtain ⟨vParent,hvParent⟩:=exists_nat_ge (2*((max Mhost Mcut:ℕ):ℝ)/ε)
  let mv:=max 1 (max v₀ (max m₀ vParent))
  have hparent:vParent≤mv:=by dsimp [mv]; omega
  have hparentR:(vParent:ℝ)≤mv:=by exact_mod_cast hparent
  have hbase:2*((max Mhost Mcut:ℕ):ℝ)≤ε*vParent:=by
    simpa [mul_comm] using (div_le_iff₀ hε).mp hvParent
  have hscale:ε*vParent≤ε*mv:=mul_le_mul_of_nonneg_left hparentR hε.le
  have hhost:(Mhost:ℝ)≤(max Mhost Mcut:ℕ):=by exact_mod_cast (le_max_left Mhost Mcut)
  have hcut:(Mcut:ℝ)≤(max Mhost Mcut:ℕ):=by exact_mod_cast (le_max_right Mhost Mcut)
  refine ⟨mv,?_,?_,?_,?_,?_⟩
  · dsimp [mv]; omega
  · dsimp [mv]; omega
  · dsimp [mv]; omega
  · linarith
  · linarith
end Oberwolfach
