module

public import Oberwolfach.OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent
public import Oberwolfach.OrdinaryTriangleCommonSampleMatchingProjection
public import Oberwolfach.OrdinaryTriangleCommonSampleProjection
public import Oberwolfach.OrdinaryShiftedMatchingWithPrior

@[expose] public section
/-! A triangle common-sample witness simultaneously retains the original
prior, the actual matching core, and the corrected protected reservoir. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_fine_sample_matching_reservoir_with_parent
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Pmatch:SimpleGraph (Fin n)) (D vsize d:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε vsize) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (εR εH pR pH θsample κ αcut pmin δcap βe βh b Bweight ηHub tpot:ℝ)
    (q s:U→Bool→ℝ) (j:Bool)
    (weight:∀i,markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ)
    (m aK bK:ℕ) (ξCorr κfine aLoad:ℝ) (mMatch Kmatch:ℕ) (p₂ k₂:ℝ)
    (wM:MarkedWheel (Prod.fst:(Fin n)×(Fin n)→(Fin n)) Prod.snd Prod.fst Prod.snd mMatch π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i:Fin Kmatch,OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)→ℝ)
    (tMatch ξMatch:ℝ)
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    (E:(Σσ,R σ)→Prop) (z:(Σσ,R σ)×(Sym2 (Fin n)→Bool))
    (Host Cuts:((Σσ,R σ)×(Sym2 (Fin n)→Bool))→Prop)
    (h:(OrdinaryTriangleCommonSampleBundle P D vsize d β ε Q π hπ εR εH pR pH θsample κ αcut pmin δcap
      βe βh b Bweight ηHub tpot s j weight m aK bK ξCorr
      (OrdinaryShiftedMatchingWithPrior Pmatch π d mMatch Kmatch p₂ k₂ q s wM wO tMatch ξMatch E) z ∧ Host z ∧ Cuts z) ∧
      OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent d κfine aLoad P D vsize β ε Q π hπ j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))):
    E z.1 ∧ OrdinaryShiftedMatchingCoreEvent Pmatch π d mMatch p₂ k₂ q s wM wO tMatch ξMatch z.1.1 ∧
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
    OrdinaryCorrectedProtectedReservoir 3 m (2*vsize) aK bK ξCorr (rawWheelGraph P raw\permutationConflictGraph π (3*d))
      (permutationConflictGraph π (3*d)) (rawWheelSpokes π d raw j)
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
      (Q.extendedIndices Q.length) (Q.extendedIndices 1) ∧ Host z ∧ Cuts z ∧
    OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent d κfine aLoad P D vsize β ε Q π hπ j raw :=by
  have hh:=ordinary_triangle_common_sample_matching_reservoir P Pmatch D vsize d β ε Q π hπ εR εH pR pH θsample
    κ αcut pmin δcap βe βh b Bweight ηHub tpot q s j weight m aK bK ξCorr mMatch Kmatch p₂ k₂ wM wO tMatch ξMatch E z h.1.1
  exact ⟨hh.1,hh.2.1,hh.2.2,h.1.2.1,h.1.2.2,h.2⟩
end Oberwolfach
