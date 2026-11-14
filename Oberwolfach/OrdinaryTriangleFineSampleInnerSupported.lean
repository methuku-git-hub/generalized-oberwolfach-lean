module

public import Oberwolfach.OrdinaryTriangleFineSampleMatchingWithInnerProjection
public import Oberwolfach.FiniteLawPositiveEventWitness
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

theorem ordinary_triangle_fine_sample_matching_reservoir_inner_supported
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
    [∀σ,Fintype (R σ)]
    (E:(Σσ,R σ)→Prop)
    (Host Cuts:((Σσ,R σ)×(Sym2 (Fin n)→Bool))→Prop)
    (Inner:RawWheelOutcome (Fin n) U Bool Bool→Prop)
    (μ:FiniteLaw ((Σσ,R σ)×(Sym2 (Fin n)→Bool))) (a:ℝ) (ha:a<1)
    (hprob:1-a≤μ.probability (fun z=>((OrdinaryTriangleCommonSampleBundle P D vsize d β ε Q π hπ εR εH pR pH θsample κ αcut pmin δcap
      βe βh b Bweight ηHub tpot s j weight m aK bK ξCorr
      (OrdinaryShiftedMatchingWithPrior Pmatch π d mMatch Kmatch p₂ k₂ q s wM wO tMatch ξMatch E) z ∧ Host z ∧ Cuts z) ∧
      Inner (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent d κfine aLoad P D vsize β ε Q π hπ j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)))):
    ∃z,0<μ.mass z ∧
    OrdinaryTriangleCommonSampleBundle P D vsize d β ε Q π hπ εR εH pR pH θsample κ αcut pmin δcap
      βe βh b Bweight ηHub tpot s j weight m aK bK ξCorr
      (OrdinaryShiftedMatchingWithPrior Pmatch π d mMatch Kmatch p₂ k₂ q s wM wO tMatch ξMatch E) z ∧
    E z.1 ∧ OrdinaryShiftedMatchingCoreEvent Pmatch π d mMatch p₂ k₂ q s wM wO tMatch ξMatch z.1.1 ∧
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
    OrdinaryCorrectedProtectedReservoir 3 m (2*vsize) aK bK ξCorr (rawWheelGraph P raw\permutationConflictGraph π (3*d))
      (permutationConflictGraph π (3*d)) (rawWheelSpokes π d raw j)
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
      (Q.extendedIndices Q.length) (Q.extendedIndices 1) ∧ Host z ∧ Cuts z ∧
    OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent d κfine aLoad P D vsize β ε Q π hπ j raw ∧ Inner raw :=by
  obtain ⟨z,hz,hevent⟩:=finiteLaw_positive_mass_witness_of_event μ _ (lt_of_lt_of_le (by linarith) hprob)
  have hh:=ordinary_triangle_fine_sample_matching_reservoir_with_inner P Pmatch D vsize d β ε Q π hπ εR εH pR pH θsample
    κ αcut pmin δcap βe βh b Bweight ηHub tpot q s j weight m aK bK ξCorr κfine aLoad mMatch Kmatch p₂ k₂
    wM wO tMatch ξMatch E z Host Cuts Inner ⟨⟨hevent.1.1,hevent.2⟩,hevent.1.2⟩
  exact ⟨z,hz,hevent.1.1.1,hh⟩
end Oberwolfach
