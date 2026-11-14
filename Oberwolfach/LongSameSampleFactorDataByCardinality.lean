module

public import Oberwolfach.LongSameSampleProtectedProbabilityTransfer

@[expose] public section
/-! Express the same-sample residual and factor continuation directly for
an arbitrary original factor-family size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longCardDataFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n
local instance (priority := 2000) longCardDataSix:DecidableEq (Fin 6):=instDecidableEqFin 6
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

def LongMatchingSameSampleFactorDataByCardinality
    {n qCount:ℕ} [Nonempty (Fin n)] (S P:SimpleGraph (Fin n))
    (F:Fin qCount→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (z:MarkedExpandedActualOutcome (U:=Fin qCount) π d) (M:Fin n→Fin n→ℕ):Prop :=
    let raw:RawMarkedOutcome (Fin n) (Fin qCount) Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let t:=startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)
    let J:=z.2;
    (∃(Pack:Finset (Sym2 (Fin n))) (Enew:Fin qCount→Finset (Sym2 (Fin n)))
      (A:Finset (Fin n×Fin n)) (R:Fin qCount→Finset (Fin n)),
      LongFactorComplementProvenance F S P π d (r+4) raw t J Pack Enew A R ∧
      ∃Small:SimpleGraph (Fin n),Small.edgeFinset=A.image (fun a=>s(a.1,a.2)) ∧
      ∃(σ:Sym2 (Fin n)→Option (Bool×Bool))
        (T:Finset {a:Fin n×Fin n // longEligibleResidualArc M Small ⊥ a}),
      (∀mark x y,markedPhysicalRim P π (3*d) σ mark x y=1 ↔
        if mark then ∃e:residualMarkedArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧π.symm e.val.val.2=y
        else ∃e:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧e.val.val.2=y) ∧
      let Y:=fun u=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J u=>d) Subtype.val
      let H₀:=fun v u=>v∈R u\Y u
      let HK:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false true true
      let E:=MarkedSampleArc P π (3*d) σ false
      let K':=MarkedSampleArc P π (3*d) σ true;
      HasResourceDecomposition (markedWheelPhysicalResources (tail:=fun e:E=>e.val.1) (head:=fun e:E=>e.val.2)
        (ktail:=fun e:K'=>e.val.1) (khead:=fun e:K'=>e.val.2) (m:=r+4) (π:=π) (b:=3*d) (H₀:=H₀) (Hₖ:=HK))
        (markedDecompositionTarget (markedPhysicalRimSet (fun e:E=>e.val.1) (fun e:E=>e.val.2)
          (fun e:K'=>e.val.1) (fun e:K'=>e.val.2) π) H₀ HK))


def LongTerminalMatchingFactorContinuationByCardinality
    {n qCount:ℕ} [Nonempty (Fin n)] (P:SimpleGraph (Fin n))
    (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d r:ℕ) (z:MarkedExpandedActualOutcome (U:=Fin qCount) π d)
    (I:Finset (Fin n)) (ξ:ℝ) (K:ℕ) (θ Dmatch alpha γ eps Δ βList:ℝ)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×Fin qCount))):Prop :=
  ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card (Fin qCount))→
    (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
    (∀x∈I,∀y∈I,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
    markedResourceRimGraph C≤S→
    ∃(M:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n)),
      LongClassMatchingDeletionWitness Δ P π d r z I K θ Dmatch alpha γ eps βList F hF weight w D₀ C S M Del ∧
      LongMatchingSameSampleFactorDataByCardinality S P F π d r z M

end Oberwolfach
