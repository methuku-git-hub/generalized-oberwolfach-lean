module

public import Oberwolfach.MarkedFixedVortexBaselineGeometry
public import Oberwolfach.MarkedAdaptiveCanonicalCentres
public import Oberwolfach.MarkedAdaptiveLevelBalances

@[expose] public section
/-! Canonical vortex centres satisfy all exact adaptive density identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fixed_vortex_canonical_densities
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (G:SimpleGraph V) (D m r:ℕ) (β ε ρ₀ s₀:ℝ)
    (Q:Vortex U G D β ε m) (hρ₀:0<ρ₀) (hρ:ρ₀ ≤ initialIndexDensity U D):
    let B:=markedVortexInnerHubs Q
    let Z:=markedVortexHubType Q
    let dens:=initialIndexDensity U D
    let p:=dens*s₀/2
    let k:=dens*(s₀/((r+4:ℕ):ℝ))/2
    let Dbal:=fun i=>2*((B i).card:ℝ)/dens
    let Dload:=fun i=>2*(Fintype.card (Z i):ℝ)/dens
    ∀i,
      p*Dbal i=s₀*(B i).card ∧
      k*Dbal i=(s₀/((r+4:ℕ):ℝ))*(B i).card ∧
      (Fintype.card (Z i):ℝ)*(s₀/((r+4:ℕ):ℝ))=Dload i*k ∧
      (Fintype.card (Z i):ℝ)*(s₀/((r+4:ℕ):ℝ))*((r+4:ℕ):ℝ)=Dload i*p := by
  intro B Z dens p k Dbal Dload i
  have hdens:0<dens:=hρ₀.trans_le hρ
  have hc:=(marked_adaptive_canonical_centre dens s₀ ((B i).card:ℝ) hdens)
  have hl:=(marked_adaptive_canonical_load dens s₀ (Fintype.card (Z i):ℝ) hdens)
  have hh:=marked_adaptive_level_balances dens s₀ ((r+4:ℕ):ℝ) (Dbal i) (Dload i)
    ((B i).card:ℝ) (Fintype.card (Z i):ℝ) (by positivity) hc hl
  exact ⟨hc,hh.1,hh.2.1,hh.2.2⟩
end Oberwolfach
