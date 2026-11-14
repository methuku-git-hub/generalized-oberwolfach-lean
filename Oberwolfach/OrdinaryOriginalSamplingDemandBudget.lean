module

public import Oberwolfach.OrdinaryAssignedLocalExpressionBeforeGeometry
public import Oberwolfach.OrdinaryExactSamplingUnassignedUpper

@[expose] public section
/-! Under the original assigned sampling recipe, the local post-matching
expression fits a later proportional placement rate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_sampling_demand_budget
    (α cap:ℝ) (hα:0<α) (hcap:0<cap):
    ∃ε:ℝ,0<ε ∧ ε ≤ cap ∧
    ∀{n q K D:ℕ} (hn:0<n) (hD:0<D)
      (F:Fin q→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
      (hK:0<K) (i₀:Fin K) (rsv θ ρ₀ smin:ℝ) (m d:ℕ)
      (hm:7 ≤ m) (hd:2 ≤ d) (hs0:0 ≤ rsv) (hs1:rsv ≤ 1/100)
      (hθ:0<θ) (hθ1:θ ≤ 1/100) (hda:1/θ ≤ d)
      (hρ₀:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity (Fin q) D) (hρhi:initialIndexDensity (Fin q) D ≤ 1)
      (S:Set ℕ) (hS:∀w,AllowedCycleLengths (F w) S)
      (hClass:OrdinaryClassReserveBound F hF i₀ rsv)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d)
      (Inner:Finset (Fin n)) (b a γ ζ edit LF:ℝ),
      min (α/4096) (1/2:ℝ)*θ ≤ b → (Inner.card:ℝ) ≤ ε*n → a ≤ b/16 → γ ≤ θ →
      0 ≤ ζ → ζ ≤ θ → edit ≤ b*n/16 → ((6*d+4:ℕ):ℝ) ≤ b*n/16 → 2*LF ≤ b*n/16 →
      edit+(max (a*n) (γ*Inner.card)+sampling.u*Inner.card+3*(ζ*Inner.card)+
        (6*d+4:ℕ)+edit+LF)+LF ≤ b*n :=by
  obtain ⟨ε,hε,hεcap,hbudget⟩:=ordinary_assigned_local_expression_before_geometry α cap hα hcap
  refine ⟨ε,hε,hεcap,?_⟩
  intro n q K D hn hD F hF hK i₀ rsv θ ρ₀ smin m d hm hd hs0 hs1 hθ hθ1 hda hρ₀ hρlo hρhi S hS hClass sampling Inner b a γ ζ edit LF
    hb hinner ha hγ hζ hζθ he haux hLF
  have hc:8 ≤ (m:ℝ)+1:=by exact_mod_cast (show 8 ≤ m+1 by omega)
  have hρ:0 < initialIndexDensity (Fin q) D:=hρ₀.trans_le hρlo
  have hu:=ordinary_exact_sampling_unassigned_upper hn hD F hF K hK i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d hd
    hs0 hs1 hθ hθ1 hc hda hρ hρhi S hS hClass sampling
  have hI:0 ≤ (Inner.card:ℝ):=by positivity
  have ht:ζ*Inner.card ≤ θ*Inner.card:=mul_le_mul_of_nonneg_right hζθ hI
  exact hbudget n Inner.card θ b a γ sampling.u (ζ*Inner.card) edit edit LF ((6*d+4:ℕ):ℝ)
    hI hθ.le hb hinner ha hγ hu ht he haux he hLF
end Oberwolfach
