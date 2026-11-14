module

public import Oberwolfach.LongEveryClassSameDeletionReady
public import Oberwolfach.LongEligibleResidualTypedHost

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance matchedEligibleTypedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_matching_witness_eligible_residual_typed_host
    {n d r K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (T:Finset (Fin n))
    (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ G π d r z T K θ D alpha γ eps βList F hF weight w D₀ C S M Del):
    ∀Small:SimpleGraph (Fin n),
    let P:=longResidualHostArc M Small (longOrdinaryIneligibleGraph G π d)
    ∀Tmark:Finset {e:(Fin n)×(Fin n) // P e},(∀e∈Tmark,longMarkedArcEligible π d e.val)→
    let E:=residualOrdinaryArc P Tmark
    let Kmark:=residualMarkedArc P Tmark
    let tail:=fun e:E=>e.val.val.1
    let head:=fun e:E=>e.val.val.2
    let ktail:=fun e:Kmark=>e.val.val.1
    let khead:=fun e:Kmark=>π.symm e.val.val.2
    Function.Injective (markedPhysicalEdge tail head ktail khead π) ∧
    (∀e:E,¬PermutationClose π (3*d) (tail e) (head e)∧G.Adj (tail e) (head e)) ∧
    (∀e:Kmark,¬PermutationClose π (3*d) (ktail e) (khead e)∧G.Adj (ktail e) (π (khead e))):=by
  intro Small P Tmark hEligible E Kmark tail head ktail khead
  obtain ⟨hphys,hbal,hD,hsub,hcorrect,hdeg,hprot,hsel,hK,hhost,hmix,hlists⟩:=hw
  exact long_eligible_residual_typed_host_properties G S Small π d M hphys hhost Tmark hEligible
end Oberwolfach
