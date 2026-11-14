module

public import Oberwolfach.OrdinaryOriginalSamplingEarlyExpression
public import Oberwolfach.OrdinaryPostmatchingUniformEditRate

@[expose] public section

/-! The edit rate and large-size threshold can be selected uniformly before
the sample, its admissible edits, and the actual factor family are known. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_early_uniform_edit_sampling_budget
    (α ε θ bList bRate bMatch a γ ζ:ℝ) (d m:ℕ)
    (hlocal:∀(n:ℕ) (inner θ' b a' γ' u t edit del LF aux:ℝ),
      0 ≤ inner → 0 ≤ θ' → min (α/4096) (1/2:ℝ)*θ' ≤ b →
      inner ≤ ε*n → a' ≤ b/16 → γ' ≤ θ' → u ≤ 2*θ' → t ≤ θ'*inner →
      edit ≤ b*n/16 → aux ≤ b*n/16 → del ≤ b*n/16 → 2*LF ≤ b*n/16 →
      edit+(max (a'*n) (γ'*inner)+u*inner+3*t+aux+del+LF)+LF ≤ b*n)
    (hList:0<bList) (hRate:0<bRate) (hMatch:0<bMatch)
    (hm:7≤m) (hd:2≤d) (hθ:0<θ) (hθ1:θ≤1/100) (hda:1/θ≤d)
    (hb:min (α/4096) (1/2:ℝ)*θ≤bRate) (ha:a≤bRate/16)
    (hγ:γ≤θ) (hζ0:0≤ζ) (hζ:ζ≤θ):
    ∃ξ:ℝ,0<ξ ∧ ξ≤bList/8 ∧ ξ≤bRate/16 ∧ ξ≤bMatch ∧
    ∃N:ℕ,∀n:ℕ,N≤n→0<n→∀{q K D:ℕ},0<D→
      ∀(F:Fin q→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2),0<K→
      ∀(i₀:Fin K) (rsv ρ₀ smin:ℝ),0 ≤ rsv → rsv ≤ 1/100 → 0<ρ₀ →
      ρ₀ ≤ initialIndexDensity (Fin q) D → initialIndexDensity (Fin q) D≤1 →
      ∀(S:Set ℕ), (∀w,AllowedCycleLengths (F w) S)→OrdinaryClassReserveBound F hF i₀ rsv→
      ∀(sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d)
       (Inner:Finset (Fin n)),(Inner.card:ℝ)≤ε*n→
      ξ*n+(max (a*n) (γ*Inner.card)+sampling.u*Inner.card+3*(ζ*Inner.card)+
        (6*d+4:ℕ)+ξ*n+2*((3*d:ℕ):ℝ))+2*((3*d:ℕ):ℝ)≤bRate*n :=by
  obtain ⟨ξ,hξ,hξlist,hξrate,hξmatch,N,hN⟩:=
    ordinary_postmatching_uniform_edit_rate bList bRate bMatch d hList hRate hMatch
  refine ⟨ξ,hξ,hξlist,hξrate,hξmatch,N,?_⟩
  intro n hn hnpos q K D hD F hF hK i₀ rsv ρ₀ smin hrs0 hrs1 hρ₀ hρlo hρhi S hS hClass sampling Inner hinner
  obtain ⟨haux,hLF⟩:=hN n hn
  have hedit:ξ*n≤bRate*n/16:=by
    have hh:ξ*n≤(bRate/16)*n:=mul_le_mul_of_nonneg_right hξrate (by positivity)
    linarith
  apply ordinary_original_sampling_early_expression α ε hlocal hnpos hD F hF hK i₀ rsv θ ρ₀ smin m d
    hm hd hrs0 hrs1 hθ hθ1 hda hρ₀ hρlo hρhi S hS hClass sampling Inner bRate a γ ζ (ξ*n)
    (2*((3*d:ℕ):ℝ)) hb hinner ha hγ hζ0 hζ hedit ?_ ?_
  · linarith
  · linarith
end Oberwolfach
