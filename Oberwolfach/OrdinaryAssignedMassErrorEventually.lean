module

public import Oberwolfach.OrdinaryMatchingMassErrorEventually
public import Oberwolfach.OrdinaryAssignedKeptMassBound

@[expose] public section
/-! The fixed-rate mass-error estimate applies to the actual ordinary
factor frequencies and marked probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_matching_mass_error_eventually
    (m d:ℕ) (hd:0<d) (err:ℝ) (herr:0<err):
    ∃N:ℕ,∀n≥N,0<n→∀(U:Type) [Fintype U]
      (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
      (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ:ℝ) (hrs:0≤rsv)
      (hrsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀)
      (u:U) (hQ:(∑g:Bool,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g)≤1/8)
      (ζ matchErr:ℝ) (hζ:0≤ζ) (he:0≤matchErr)
      (hrate:1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζ+matchErr≤err/2),
      (n:ℝ)*(∑g:Bool,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g)/d+
        (((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n)+
        matchErr*n*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)≤err*n:=by
  obtain ⟨N,hN⟩:=ordinary_matching_full_mass_error_eventually m d hd err herr
  refine ⟨N,?_⟩
  intro n hn hn0 U _ F hF Allowed hAllowed K hK i₀ rsv θ hrs hrsclass hclass u hQ ζ matchErr hζ he hrate
  have hfrac:∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i≤1:=by
    have hh:=ordinary_assigned_kept_mass_le_unreserved hn0 F hF Allowed hAllowed K hK i₀ rsv θ hrs hrsclass hclass u
    linarith
  exact hN n hn _ _ ζ matchErr hQ hfrac hζ he hrate
end Oberwolfach
