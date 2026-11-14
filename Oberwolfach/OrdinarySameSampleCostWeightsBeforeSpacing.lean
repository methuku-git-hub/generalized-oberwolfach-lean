module

public import Oberwolfach.OrdinaryVortexUniformEditCostBeforeSpacing
public import Oberwolfach.OrdinarySameSampleSelectedCostWeights
public import Oberwolfach.OrdinaryVortexUniformEditCostEvents
public import Oberwolfach.FiniteLawPositiveLowerBoundWitness

@[expose] public section
/-! Preserve any prior event, including the corrected reservoir, while
specializing all-edit weights to the actual selected level costs on the
same sample. A positive lower bound supplies an actual supported witness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {P:SimpleGraph V} {D mv:ℕ} {β ε:ℝ} (Q:Vortex U P D β ε mv)
  (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)

theorem ordinary_same_sample_selected_cost_weights_before_spacing
    (ε ρ₀ cap:ℝ) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hcap:0<cap):
    ∃rate:ℝ,0<rate ∧ ∀(d:ℕ),∀β:ℝ,0 ≤ β  →  β ≤ 1/4  →  ∃m₀:ℕ,1 ≤ m₀ ∧
    ∀(V U Γ Color Ω:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Ω]
      [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D mv:ℕ),P.IsRegularOfDegree D  →  0<Fintype.card V  → 
      (Fintype.card V:ℝ)/2 ≤ D  →  ρ₀ ≤ initialIndexDensity U D  →  initialIndexDensity U D ≤ 1  →  m₀ ≤ mv  → 
    ∀(Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (m:ℕ) (pR pH βe βh b B η:ℝ) (density tR tH:ℕ → ℝ)
      (s:U → Color → ℝ) (j:Color) (rateActual:ℝ),0 ≤ rateActual  →  rateActual ≤ rate  → 
    ∀(μ:FiniteLaw Ω) (E:Ω → Prop) (σ:Ω → RawWheelOutcome V U Γ Color) (bound:ℝ),
    bound ≤ μ.probability (fun z=>E z ∧ OrdinaryUniformEditWeightEvents Q π hπ m d pR pH cap βe βh b B η
      density tR tH s j (σ z))  → 
    let Good:Ω → Prop:=fun z=>E z ∧ OrdinaryUniformEditWeightEvents Q π hπ m d pR pH cap βe βh b B η
      density tR tH s j (σ z) ∧ OrdinarySelectedCostWeightEvents Q π hπ m d pR pH cap βe βh b B η rateActual
        density tR tH s j (σ z);
    bound ≤ μ.probability Good ∧ (0<bound  →  ∃z,0<μ.mass z ∧ Good z) :=by
  obtain ⟨rate,hrate,hcost⟩:=ordinary_vortex_uniform_edit_cost_events_before_spacing ε ρ₀ cap hε hε1 hρ₀ hcap
  refine ⟨rate,hrate,?_⟩
  intro d β hβ hβ1
  obtain ⟨m₀,hm₀,hcost⟩:=hcost d β hβ hβ1
  refine ⟨m₀,hm₀,?_⟩
  intro V U Γ Color Ω _ _ _ _ _ _ _ P D mv hreg hn hD hρlo hρhi hm Q π hπ m pR pH βe βh b B η density tR tH s j
    rateActual hrateActual hrateBound μ E σ bound hprob Good
  have hmono:μ.probability (fun z=>E z ∧ OrdinaryUniformEditWeightEvents Q π hπ m d pR pH cap βe βh b B η
      density tR tH s j (σ z))  ≤  μ.probability Good:=by
    apply finiteLaw_probability_mono
    intro z hz
    refine ⟨hz.1,hz.2,?_⟩
    exact hcost V U Γ Color P D mv hreg hn hD hρlo hρhi hm Q π hπ m pR pH βe βh b B η density tR tH s j
      (σ z) rateActual hrateActual hrateBound hz.2
  have hout:=hprob.trans hmono
  exact ⟨hout,fun hb=>finiteLaw_positive_lower_bound_witness μ Good bound hb hout⟩
end Oberwolfach
