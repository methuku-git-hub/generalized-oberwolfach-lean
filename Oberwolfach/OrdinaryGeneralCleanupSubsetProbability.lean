module

public import Oberwolfach.OrdinaryGeneralSameSampleProbability
public import Oberwolfach.OrdinaryBoundarySubsetEventMono

@[expose] public section
/-! Preserve the safe-subset cleanup probability when using the full-set
    event required by the existing matching and completion interface. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_general_cleanup_subset_probability
    (m:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (η ell t ν:ℝ) (D:OrdinaryRootCoverData Q F H X T Z W (m+1) η ell)
    (p βe βh b:ℝ) (μ:FiniteLaw (Sym2 (V⊕U)→Bool))
    (hprob:b≤μ.probability (fun σ=>
      Nonempty (OrdinaryRootFirstCleanupOutcome Q F H X T Z W (m+1) η ell t ν D σ) ∧
      OrdinaryBoundaryExtensionGood (Q\D.rim) (fun v u=>H v u∧¬D.spokes v u) (X\T) βe p σ ∧
      OrdinaryBoundaryHubPairGood (fun v u=>H v u∧¬D.spokes v u) Z βh p σ)):
    b≤μ.probability (OrdinaryGeneralRootFirstCleanupSample m Q F H X T Z W η ell t ν D p βe βh) :=by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  exact ⟨hσ.1,ordinary_boundary_extension_event_subset_mono (Q\D.rim)
    (fun v u=>H v u∧¬D.spokes v u) (X\T) X Finset.sdiff_subset βe p σ hσ.2.1,hσ.2.2⟩
end Oberwolfach
