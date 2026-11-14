module

public import Oberwolfach.LongMatchingReconstructionFromSameSample
public import Oberwolfach.LongTerminalRobustPreparationCertificate

@[expose] public section
/-! Express the remaining long factor continuation on the same sample,
matching, corrected encoding and protected terminal reserve. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longTerminalSameSampleFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n
local instance (priority := 2000) longTerminalSameSampleSix:DecidableEq (Fin 6):=instDecidableEqFin 6
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

def LongMatchingSameSampleFactorDataAt
    {n D:ℕ} [Nonempty (Fin n)] (S P:SimpleGraph (Fin n))
    (F:Fin (D/2)→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (z:MarkedExpandedActualOutcome (U:=Fin (D/2)) π d) (M:Fin n→Fin n→ℕ):Prop :=
    let raw:RawMarkedOutcome (Fin n) (Fin (D/2)) Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let t:=startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)
    let J:=z.2;
    (∃(Pack:Finset (Sym2 (Fin n))) (Enew:Fin (D/2)→Finset (Sym2 (Fin n)))
      (A:Finset (Fin n×Fin n)) (R:Fin (D/2)→Finset (Fin n)),
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

theorem long_terminal_same_sample_factor_continuation
    {n D:ℕ} [Nonempty (Fin n)] (hEven:Even D)
    (P:SimpleGraph (Fin n)) (F:Fin (D/2)→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d r:ℕ) (hd:2≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (z:MarkedExpandedActualOutcome (U:=Fin (D/2)) π d)
    (I:Finset (Fin n)) (Hubs:Finset (Fin (D/2))) (γLoss σLoss:ℝ) (e₀:ℕ)
    (X:Finset (Fin n)) (Z:Finset (Fin (D/2)))
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×Fin (D/2)))) (ξ:ℝ)
    (K:ℕ) (θ Dmatch alpha γ eps Δ βList:ℝ)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (hTerminal:longTerminalProtectedReserve P π d r z z.2 I Hubs γLoss σLoss e₀ X Z D₀ C)
    (hContinuation:∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card (Fin (D/2)))→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
      (∀x∈I,∀y∈I,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→
      ∃(M:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n)),
        LongClassMatchingDeletionWitness Δ P π d r z I K θ Dmatch alpha γ eps βList F hF weight w D₀ C S M Del ∧
        LongMatchingSameSampleFactorDataAt S P F π d r z M):
    ∃A:SimpleGraph (Fin n),A≤longPhysicalStateGraph P z.1 {0,1,2,3,4} ∧ A.edgeFinset.card≤e₀ ∧
      ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card (Fin (D/2)))→A≤S→
        (∀x∈I,∀y∈I,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
        (∀v,((Finset.univ.filter (fun y=>Xor (S.Adj v y) ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj v y))).card:ℝ)≤ξ*n)→
        HasFactorDecomposition S F :=by
  apply long_terminal_robust_preparation_certificate P π d r z I Hubs γLoss σLoss e₀ X Z D₀ C ξ (D/2) F hTerminal
  intro S hSP hreg hchange hinner hC
  obtain ⟨M,Del,hw,hdata⟩:=hContinuation S hSP hreg hchange hinner hC
  exact long_matching_reconstruct_from_same_sample_data hEven S P Del F hF π d r hd hnoshort z I K θ Dmatch alpha γ eps Δ βList weight w D₀ C M hw hdata
end Oberwolfach
