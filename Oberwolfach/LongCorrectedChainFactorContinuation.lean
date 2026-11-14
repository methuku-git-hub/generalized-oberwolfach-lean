module

public import Oberwolfach.LongSameSampleFactorDataFromEncoding
public import Oberwolfach.LongMatchingReconstructionFromSameSample

@[expose] public section
/-! The output of the corrected level chain reconstructs the prescribed factors
on the same sample, using the matching and complement selected for the target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longChainFactorFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n
local instance (priority := 2000) longChainFactorSix:DecidableEq (Fin 6):=instDecidableEqFin 6
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem long_corrected_chain_factor_continuation
    {n q:ℕ} [Nonempty (Fin n)] (S P Del:SimpleGraph (Fin n))
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d r:ℕ) (hd:2≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (z:MarkedExpandedActualOutcome (U:=Fin q) π d)
    (I:Finset (Fin n)) (K:ℕ) (θ Dmatch alpha γ eps Δ βList:ℝ)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×Fin q))) (M:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ P π d r z I K θ Dmatch alpha γ eps βList F hF weight w D₀ C S M Del):
    let raw:RawMarkedOutcome (Fin n) (Fin q) Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let t:=startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)
    let J:=z.2;
    ∀(Pack:Finset (Sym2 (Fin n))) (Enew:Fin q→Finset (Sym2 (Fin n)))
      (A:Finset (Fin n×Fin n)) (R:Fin q→Finset (Fin n)),
      LongFactorComplementProvenance F S P π d (r+4) raw t J Pack Enew A R→
    ∀Small:SimpleGraph (Fin n),Small.edgeFinset=A.image (fun a=>s(a.1,a.2))→
    ∀(τ:RawMarkedOutcome (Fin n) (Fin q) Bool Bool)
      (T:Finset {a:Fin n×Fin n // longEligibleResidualArc M Small ⊥ a}),
      (∀mark x y,markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
        if mark then ∃e:residualMarkedArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧π.symm e.val.val.2=y
        else ∃e:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧e.val.val.2=y)→
    let Y:=fun u=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J u=>d) Subtype.val
    let Hnew:Bool→Fin n→Fin q→Prop:=fun b v u=>if b then retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false true true v u else v∈R u\Y u
    let E:=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true;
    HasResourceDecomposition (fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (r+4) π (3*d) (Hnew false) (Hnew true)=>markedWheelPhysicalResources W)
      (markedDecompositionTarget (markedPhysicalRimSet (fun e:E=>e.val.1) (fun e:E=>e.val.2)
        (fun e:K'=>e.val.1) (fun e:K'=>e.val.2) π) (Hnew false) (Hnew true))→
    HasFactorDecomposition S F :=by
  intro raw t J Pack Enew A R hprov Small hSmall τ T hcode Y Hnew E K' hdec
  have hData:LongMatchingSameSampleFactorDataByCardinality S P F π d r z M:=by
    apply long_same_sample_factor_data_from_encoding S P F π d r z M Pack Enew A R hprov Small hSmall (fun e=>τ (Sum.inl e)) T hcode
    have hh:=hdec
    dsimp only [Hnew,Y,raw,t,J,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
    convert hh using 1 <;> congr! 12 <;> first | rfl | exact Subsingleton.elim _ _
  generalize hD:2*q=Dclass
  have hEq:Dclass/2=q:=by omega
  have hEven:Even Dclass:=by exact ⟨q,by omega⟩
  subst q
  exact long_matching_reconstruct_from_same_sample_data hEven S P Del F hF π d r hd hnoshort z I K θ Dmatch alpha γ eps Δ βList weight w D₀ C M hw hData
end Oberwolfach
