module

public import Oberwolfach.LongDualVortexEncodedActiveAndDeeper
public import Oberwolfach.LongMatchingPhysicalCorrectionFields
public import Oberwolfach.MarkedVortexFirstActiveExactRims
public import Oberwolfach.LongEncodedResidualSampleDivisibility
public import Oberwolfach.MarkedVortexActualResidualDeeperEquality

@[expose] public section
/-! The balanced residual has one encoding which preserves the selected
sample on the first active set, and transfers its exact divisibility. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite
local instance matchingVortexEncodingFin (n:ℕ):DecidableEq (Fin n):=dualVortexDeeperEncodingDecEq



theorem long_matching_vortex_encoded_active_and_deeper
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (G S Small:SimpleGraph (Fin n)) (D mm:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε mm)
    (π:Equiv.Perm (Fin n)) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (d m:ℕ) (Mhost:Fin n→Fin n→ℕ)
    (Δ:ℝ) (r K:ℕ) (θ Dmatch alpha γ eps βList:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (F:U→SimpleGraph (Fin n))
    (hF:∀u,(F u).IsRegularOfDegree 2) (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (Del:SimpleGraph (Fin n))
    (hw:LongClassMatchingDeletionWitness Δ G π d r z (Q.extendedVertices 1) K θ Dmatch alpha γ eps βList F hF weight w D₀ C S Mhost Del)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (T:Finset {e:Fin n×Fin n // longEligibleResidualArc Mhost Small ⊥ e})
    (hMarked:∀e∈T,longMarkedArcEligible π d e.val)
    (hOrd:∀e,e∉T→longOrdinaryArcEligible π d e.val)
    (hInner:∀mark x y,x∈Q.extendedVertices 1→y∈Q.extendedVertices 1→
      (markedPhysicalRim G π (3*d) (fun e=>raw (Sum.inl e)) mark x y=1 ↔
        if mark then ∃e:residualMarkedArc (longEligibleResidualArc Mhost Small ⊥) T,e.val.val.1=x∧π.symm e.val.val.2=y
        else ∃e:residualOrdinaryArc (longEligibleResidualArc Mhost Small ⊥) T,e.val.val.1=x∧e.val.val.2=y))
    (ρ:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d ρ false) t) (R:U→Finset (Fin n))
    (hspoke:∀u∈Q.extendedIndices 1,∀v∈Q.extendedVertices 1,
      (v∈R u\markedIntervalRootSet π (fun _:retainedMarkedIndex π d ρ false t J u=>d) Subtype.val ↔
        retainedRawMarkedSpokes π d ρ false t J false false false v u))
    (HK:Fin n→U→Prop) (Sp:Finset (Fin n×U))
    (hdiv:MarkedRemainderDivisible
      (fun e:residualOrdinaryArc (longEligibleResidualArc Mhost Small ⊥) T=>e.val.val.1) (fun e=>e.val.val.2)
      (fun e:residualMarkedArc (longEligibleResidualArc Mhost Small ⊥) T=>e.val.val.1) (fun e=>π.symm e.val.val.2)
      HK Finset.univ Sp m):
    ∃τ:RawMarkedOutcome (Fin n) U Bool Bool,
      (∀e,τ (Sum.inr e)=raw (Sum.inr e)) ∧
      (∀e:Sym2 (Fin n),e.toFinset⊆Q.extendedVertices 1→τ (Sum.inl e)=raw (Sum.inl e)) ∧
      (let f:=markedVortexActiveVertexEmbedding Q 1
       let g:=markedVortexNonDeeperHubToPhysical Q 0
       let ρ:=markedVortexActivePermutation Q π hπ 1;
       rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g τ)=
       rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g raw)) ∧
      (∀ (i:ℕ), 1 ≤ i →
        rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) raw=
          rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) τ ∧
        (fun b v u=>retainedRawMarkedSpokes π d ρ false t J false false b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u))=
        (fun b v u=>if b then retainedRawMarkedSpokes π d ρ false t J false false true (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u)
          else markedVortexVertexEmbedding Q i v∈R (markedVortexHubEmbedding Q i u)\markedIntervalRootSet π
            (fun _:retainedMarkedIndex π d ρ false t J (markedVortexHubEmbedding Q i u)=>d) Subtype.val)) ∧
      (∀mark x y,markedPhysicalRim G π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
        if mark then ∃e:residualMarkedArc (longEligibleResidualArc Mhost Small ⊥) T,e.val.val.1=x∧π.symm e.val.val.2=y
        else ∃e:residualOrdinaryArc (longEligibleResidualArc Mhost Small ⊥) T,e.val.val.1=x∧e.val.val.2=y) ∧
      MarkedRemainderDivisible
        (fun e:MarkedSampleArc G π (3*d) (fun e=>τ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
        (fun e:MarkedSampleArc G π (3*d) (fun e=>τ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
        HK Finset.univ Sp m :=by
  have hmatch:=long_matching_physical_correction_fields Δ G π d r z (Q.extendedVertices 1) K θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Mhost hw
  exact long_dual_vortex_encoded_active_and_deeper G S Small D mm β ε Q π hπ d m Mhost hmatch.1 hmatch.2.1 raw T hMarked hOrd hInner ρ t J R hspoke HK Sp hdiv
end Oberwolfach
