module

public import Oberwolfach.LongProtectedMatchingDeletionBudget
public import Oberwolfach.MarkedReferenceLevelThresholdMono

@[expose] public section
/-! A protected deletion of bounded edge count fits into the reserved half of the
matching budget after increasing only the host-order threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem long_card_bounded_protected_matching_deletion_with_budget
    (Δ C ξmax:ℝ) (B:ℕ) (hΔ:0<Δ) (hC:0≤C) (hmax:0<ξmax):
    ∃ξcap:ℝ,0<ξcap ∧ ξcap≤ξmax ∧ ∃N:ℕ,∀n≥N,
    ∀(U Γ Color:Type) [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color],
    ∀(P S Kbad D₀ Protected:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
      (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)
      (M:Fin n→Fin n→ℕ),
    let S₀:=longPhysicalStateGraph P ω {0,1,2,3,4};
    ∀(ξ δ:ℝ),0≤ξ→ξ≤ξcap→
      δ≤C*Real.sqrt ξ+5*(n:ℝ)^(-(1/5:ℝ))→
    S≤P→Kbad≤S→(∀x y,M x y+M y x=if S.Adj x y then 1 else 0)→
    (∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
    (∀v,((orientationDisagreementGraph S₀ (fun e=>(ω (Sum.inl e)).2) M).degree v:ℝ)≤δ*n)→
    D₀.edgeFinset.card≤B→
    (∀x y,Protected.Adj x y→(S.Adj x y↔S₀.Adj x y))→
    (∀x y,D₀.Adj x y→¬Protected.Adj x y)→
    (∀x y,(orientationDisagreementGraph S₀ (fun e=>(ω (Sum.inl e)).2) M).Adj x y→¬Protected.Adj x y)→
    ∃Del:SimpleGraph (Fin n),D₀≤Del ∧ (S₀\S)≤Del ∧
      orientationDisagreementGraph S₀ (fun e=>(ω (Sum.inl e)).2) M≤Del ∧
      (∀v,(Del.degree v:ℝ)≤Δ*n) ∧
      (∀x y,Del.Adj x y→¬Protected.Adj x y) ∧
      (∀x y,rawSelectedPhysicalRelation P π d (fun e=>ω (Sum.inl e)) x y→¬Del.Adj x y→M x y=1) ∧
      (∀x y,Kbad.Adj x y→M x y=1 ∨ M y x=1) ∧
      (∀x y,M x y=1→P.Adj x y) ∧
      (∀x y,rawMixedPhysicalArc P π d (fun e=>rawExpandedApproximateCollapse e (ω e)) x y→
        ¬Del.Adj x y→M x y=1) := by
  obtain ⟨ξcap,hξcap,hξmax,N₀,hMain⟩:=long_protected_matching_deletion_with_budget Δ C ξmax hΔ hC hmax
  obtain ⟨N₁,hN₁,hSize⟩:=bounded_card_fits_two_linear_reserves B (Δ/2) (Δ/2) (by positivity) (by positivity)
  refine ⟨ξcap,hξcap,hξmax,max N₀ N₁,?_⟩
  intro n hn U Γ Color _ _ _ _ P S Kbad D₀ Protected π d ω M
  dsimp only
  intro ξ δ hξ0 hξbound hδ hSP hKP hphysical hedit hcorrect hD₀ hprotect hD₀protect hcorrprotect
  have hB:(B:ℝ)≤(Δ/2)*n:=by
    simpa only [min_self] using hSize n (by omega)
  have hD₀real:∀v,(D₀.degree v:ℝ)≤(Δ/2)*n:=by
    intro v
    have hh:(D₀.degree v:ℝ)≤B:=by exact_mod_cast (D₀.degree_le_card_edgeFinset v).trans hD₀
    exact hh.trans hB
  exact hMain n (by omega) U Γ Color P S Kbad D₀ Protected π d ω M
    ξ δ (Δ/2) hξ0 hξbound le_rfl hδ hSP hKP hphysical hedit hcorrect hD₀real hprotect hD₀protect hcorrprotect
end Oberwolfach
