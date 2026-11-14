module

public import Oberwolfach.MarkedReferenceAfterPhysicalChanges

@[expose] public section
/-! The statistics and cut fields in the marked reference-level interface,
with their original density targets and explicit physical-change budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_changed_statistics_and_cuts
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ) (g:Γ) (j:Color)
    (rho t gamma kappa D eps alphaOld gammaOld ζ:ℝ)
    (σ τ:RawMarkedOutcome V U Γ Color) (FR:SimpleGraph V)
    (hinterval:∀ e,σ (Sum.inr e)=τ (Sum.inr e))
    (hchange:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈FR.edgeFinset)
    (hdeg:∀ v,(FR.degree v:ℝ)≤ζ*Fintype.card V) (hζ:0≤ζ)
    (herror:eps+ζ≤kappa/4) (halpha:2*gamma≤alphaOld)
    (hstep:2*ζ≤(3/2)*(gammaOld-2*gamma)*(rho*(r+4:ℝ)*t/2)^2)
    (hcut:∀ mark:Bool,ζ≤(alphaOld-2*gamma)*
      (if mark then (rho*(r+4:ℝ)*t/2)/(r+4:ℝ) else rho*(r+4:ℝ)*t/2)/4):
    let p:=rho*(r+4:ℝ)*t/2
    let k:=p/(r+4:ℝ);
    MarkedReferenceStatistics P π d g j D eps kappa gammaOld p k ((r+4:ℝ)*t) t σ→
    MarkedReferenceCutFamilies P π d g j alphaOld p k t σ→
    MarkedReferenceStatistics P π d g j D (kappa/4) kappa (2*gamma) p k ((r+4:ℝ)*t) t τ ∧
    MarkedReferenceCutFamilies P π d g j (2*gamma) p k t τ :=by
  intro p k hstats hcuts
  have hstats':=marked_reference_statistics_after_physical_change P π d g j D eps kappa gammaOld (2*gamma)
    p k ((r+4:ℝ)*t) t ζ σ τ FR hinterval hchange hdeg hstep hstats
  have hcuts':=marked_reference_cuts_after_physical_change P π d g j alphaOld (2*gamma) p k t ζ
    halpha hζ hcut σ τ FR hinterval hchange hdeg hcuts
  refine ⟨?_,hcuts'⟩
  refine ⟨⟨?_,hstats'.1.2⟩,hstats'.2⟩
  intro mark x
  have h:=hstats'.1.1 mark x
  have hh:=mul_le_mul_of_nonneg_right herror (Nat.cast_nonneg (Fintype.card V))
  exact ⟨h.1.trans hh,h.2.trans hh⟩
end Oberwolfach
