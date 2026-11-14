module

public import Oberwolfach.OrdinaryGeneralRootFreeCleanupSubsetProbability
public import Oberwolfach.OrdinarySampledCoverDegree
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

def OrdinaryGeneralRootFreeSampledCoverCleanupSample (m:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W (m+1) η ell) (p βe βh δsample:ℝ)
    (σ:Sym2 (V⊕U)→Bool):Prop :=
  OrdinaryGeneralRootFreeCleanupSample m Q F H X T Z W η ell t ν D p βe βh σ ∧
  OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample σ

theorem ordinary_general_root_free_sampled_cover_cleanup_subset_probability
    (m:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (η ell t ν:ℝ) (D:OrdinaryRootCoverData Q F H X T Z W (m+1) η ell)
    (p βe βh δsample b:ℝ) (μ:FiniteLaw (Sym2 (V⊕U)→Bool))
    (hprob:b≤μ.probability (fun σ=>
      ((∃O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W (m+1) η ell t ν D σ,
        Disjoint (ordinaryPhysicalGraph (wheelFamilyRim O.cleanup.wheels) (wheelFamilySpokes O.cleanup.wheels))
          (ordinaryDeepRootStar T W)) ∧
      OrdinaryBoundaryExtensionGood (Q\D.rim) (fun v u=>H v u∧¬D.spokes v u) (X\T) βe p σ ∧
      OrdinaryBoundaryHubPairGood (fun v u=>H v u∧¬D.spokes v u) Z βh p σ) ∧
      OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample σ)):
    b≤μ.probability (OrdinaryGeneralRootFreeSampledCoverCleanupSample m Q F H X T Z W η ell t ν D p βe βh δsample) :=by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  exact ⟨⟨hσ.1.1,ordinary_boundary_extension_event_subset_mono (Q\D.rim)
    (fun v u=>H v u∧¬D.spokes v u) (X\T) X Finset.sdiff_subset βe p σ hσ.1.2.1,hσ.1.2.2⟩,hσ.2⟩
end Oberwolfach
