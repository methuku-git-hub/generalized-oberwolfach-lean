module

public import Oberwolfach.OrdinarySelectedCostRate

@[expose] public section
/-! Preserve the cost-weight threshold when joining the beta-dependent
certificate thresholds before choosing a single terminal size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinarySelectedCostAtSpacing (ε ρ₀ cap:ℝ) (d:ℕ) (rate β:ℝ) (m₀:ℕ):Prop :=
    1≤m₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D mv:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤mv→
    ∀(Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (m:ℕ) (pR pH βe βh b B η:ℝ) (density tR tH:ℕ→ℝ)
      (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
      (rateActual:ℝ),0 ≤ rateActual → rateActual ≤ rate→
    OrdinaryUniformInnerHubEvent m P D mv d β ε Q π hπ pR pH βe βh b B η cap density tR tH s j σ→
    OrdinarySelectedCostWeightEvents Q π hπ m d pR pH cap βe βh b B η rateActual density tR tH s j σ

theorem ordinary_selected_cost_join_threshold_payload
    (ε ρ₀ cap:ℝ) (d:ℕ) (rate βcap δInitial δDeep δedit:ℝ)
    (hcost:OrdinarySelectedCostRate ε ρ₀ cap d rate)
    (Payload:ℝ→ℕ→ℕ→Prop)
    (hPayload:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→∃m₀ Nmin:ℕ,Payload β m₀ Nmin):
    ∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
    ∃m₀ Nmin:ℕ,∃mCert mCost:ℕ,mCert≤m₀ ∧ mCost≤m₀ ∧
      Payload β mCert Nmin ∧ OrdinarySelectedCostAtSpacing ε ρ₀ cap d rate β mCost :=by
  intro β hβ hβ1 hβcap hInitial hDeep hEdit
  obtain ⟨mCert,Nmin,hcert⟩:=hPayload β hβ hβ1 hβcap hInitial hDeep hEdit
  obtain ⟨mCost,hmCost,hcost⟩:=hcost β hβ.le hβ1
  exact ⟨max mCert mCost,Nmin,mCert,mCost,le_max_left _ _,le_max_right _ _,hcert,hmCost,hcost⟩
end Oberwolfach
