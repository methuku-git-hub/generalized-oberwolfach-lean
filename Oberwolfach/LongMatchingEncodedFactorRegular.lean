module

public import Oberwolfach.LongMatchingWitnessRegular
public import Oberwolfach.LongMatchingEncodedFactorReconstruction
public import Oberwolfach.LongEncodedSampleProvenanceFactorDecomposition
public import Oberwolfach.LongEveryClassSameDeletionReady

@[expose] public section
/-! A wheel decomposition of the exact corrected encoding reconstructs the
prescribed factors using the same class, matching and complement provenance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance matchingRegularReconstructionFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem long_matching_encoded_factor_reconstruction_from_witness
    {n D:ℕ} [Nonempty (Fin n)] (hEven:Even D) (S P Del:SimpleGraph (Fin n))
    (F:Fin (D/2)→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d r:ℕ) (hd:2≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (z:MarkedExpandedActualOutcome (U:=Fin (D/2)) π d)
    (I:Finset (Fin n)) (K:ℕ) (θ Dmatch alpha γ eps Δ βList:ℝ)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×Fin (D/2)))) (M:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ P π d r z I K θ Dmatch alpha γ eps βList F hF weight w D₀ C S M Del):
    let raw:RawMarkedOutcome (Fin n) (Fin (D/2)) Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let t:=startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)
    let J:=z.2;
    ∀(Pack:Finset (Sym2 (Fin n))) (Enew:Fin (D/2)→Finset (Sym2 (Fin n)))
      (A:Finset (Fin n×Fin n)) (R:Fin (D/2)→Finset (Fin n)),
    LongFactorComplementProvenance F S P π d (r+4) raw t J Pack Enew A R→
    ∀Small:SimpleGraph (Fin n),Small.edgeFinset=A.image (fun a=>s(a.1,a.2))→
    ∀(σ:Sym2 (Fin n)→Option (Bool×Bool))
      (T:Finset {a:Fin n×Fin n // longEligibleResidualArc M Small ⊥ a}),
    (∀mark x y,markedPhysicalRim P π (3*d) σ mark x y=1 ↔
      if mark then ∃e:residualMarkedArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧π.symm e.val.val.2=y
      else ∃e:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧e.val.val.2=y)→
    let Y:=fun u=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J u=>d) Subtype.val
    let H₀:=fun v u=>v∈R u\Y u
    let HK:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false true true
    let E:=MarkedSampleArc P π (3*d) σ false
    let K':=MarkedSampleArc P π (3*d) σ true;
    HasResourceDecomposition (markedWheelPhysicalResources (tail:=fun e:E=>e.val.1) (head:=fun e:E=>e.val.2)
      (ktail:=fun e:K'=>e.val.1) (khead:=fun e:K'=>e.val.2) (m:=r+4) (π:=π) (b:=3*d) (H₀:=H₀) (Hₖ:=HK))
      (markedDecompositionTarget (markedPhysicalRimSet (fun e:E=>e.val.1) (fun e:E=>e.val.2)
        (fun e:K'=>e.val.1) (fun e:K'=>e.val.2) π) H₀ HK) →
    HasFactorDecomposition S F :=by
  intro raw t J Pack Enew A R hprov Small hSmall σ T hcode Y H₀ HK E K' hdec
  have hh:=long_matching_witness_regular Δ P S Del π d r z I K θ Dmatch alpha γ eps βList F hF weight w D₀ C M hw
  have htwo:2*(D/2)=D:=by have hhEven:=hEven.two_dvd; omega
  have hS:S.IsRegularOfDegree D:=by simpa only [Fintype.card_fin,htwo] using hh
  exact long_matching_encoded_factor_reconstruction hEven S P Del hS F hF π d r hd hnoshort z I K θ Dmatch alpha γ eps Δ βList weight w D₀ C M hw
    Pack Enew A R hprov Small hSmall σ T hcode hdec
end Oberwolfach
