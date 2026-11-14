module

public import Oberwolfach.LongEveryClassSameDeletionReady
public import Oberwolfach.LongMarkedResidualIncomingChange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_matching_witness_correction_bound
    {n d r K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (T:Finset (Fin n))
    (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ G π d r z T K θ D alpha γ eps βList F hF weight w D₀ C S M Del):
    orientationDisagreementGraph (longPhysicalStateGraph G z.1 {0,1,2,3,4}) (fun e=>(z.1 (Sum.inl e)).2) M≤Del ∧
    (∀v,(Del.degree v:ℝ)≤Δ*n):=by
  constructor
  · intro x y h
    apply hw.2.2.2.2.1
    simpa only [orientationDisagreementGraph,longPhysicalStateGraph,sampledOrientation,Finset.mem_insert,Finset.mem_singleton] using h
  · exact hw.2.2.2.2.2.1
end Oberwolfach
