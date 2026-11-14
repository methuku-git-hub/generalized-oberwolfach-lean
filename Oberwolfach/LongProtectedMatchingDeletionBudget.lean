module

public import Oberwolfach.LongOrientationDeletionReserve
public import Oberwolfach.LongClassProtectedMatchingAfterCorrection

@[expose] public section
/-! Convert the manuscript's graph-change and orientation errors into the
exact protected physical-deletion budget required by matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_protected_matching_deletion_with_budget
    (Δ C ξmax:ℝ) (hΔ:0<Δ) (hC:0≤C) (hmax:0<ξmax):
    ∃ξcap:ℝ,0<ξcap ∧ ξcap≤ξmax ∧ ∃N:ℕ,∀n≥N,
    ∀(U Γ Color:Type) [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color],
    ∀(P S Kbad D₀ Protected:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
      (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)
      (M:Fin n→Fin n→ℕ),
    let S₀:=longPhysicalStateGraph P ω {0,1,2,3,4};
    ∀(ξ δ η:ℝ),0≤ξ→ξ≤ξcap→η≤Δ/2→
      δ≤C*Real.sqrt ξ+5*(n:ℝ)^(-(1/5:ℝ))→
    S≤P→Kbad≤S→(∀x y,M x y+M y x=if S.Adj x y then 1 else 0)→
    (∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
    (∀v,((orientationDisagreementGraph S₀ (fun e=>(ω (Sum.inl e)).2) M).degree v:ℝ)≤δ*n)→
    (∀v,(D₀.degree v:ℝ)≤η*n)→
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
  obtain ⟨ξcap,hξcap,hξmax,N,hscale⟩:=long_orientation_deletion_scale_with_reserve Δ C ξmax hΔ hC hmax
  refine ⟨ξcap,hξcap,hξmax,N,?_⟩
  intro n hn U Γ Color _ _ _ _ P S Kbad D₀ Protected π d ω M
  dsimp only
  intro ξ δ η hξ0 hξbound hη hδ hSP hKP hphysical hedit hcorrect hD₀ hprotect hD₀protect hcorrprotect
  have hsum:η+ξ+δ≤Δ:=by
    have h:=hscale n hn ξ η hξ0 hξbound hη
    linarith
  obtain ⟨Del,hD,hedits,hinc,hdegree,hDelProtect,hselected,hbad,hP,hmixed⟩:=
    long_class_protected_matching_after_correction P S Kbad D₀ Protected π d ω M ξ δ η
      hSP hKP hphysical (by simpa only [Fintype.card_fin] using hedit)
      (by simpa only [Fintype.card_fin] using hcorrect) (by simpa only [Fintype.card_fin] using hD₀)
      hprotect hD₀protect hcorrprotect
  refine ⟨Del,hD,hedits,hinc,?_,hDelProtect,hselected,hbad,hP,hmixed⟩
  intro v
  have hh:=hdegree v
  simp only [Fintype.card_fin] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hsum (by positivity))
end Oberwolfach
