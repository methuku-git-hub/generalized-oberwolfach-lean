module

public import Oberwolfach.LongSameSampleFactorDataByCardinality

@[expose] public section
/-! The corrected encoding and its wheel decomposition give the exact
factor data for the same original sample and matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longDataEncodingFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n
local instance (priority := 2000) longDataEncodingSix:DecidableEq (Fin 6):=instDecidableEqFin 6
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem long_same_sample_factor_data_from_encoding
    {n q:ℕ} [Nonempty (Fin n)] (S P:SimpleGraph (Fin n))
    (F:Fin q→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (z:MarkedExpandedActualOutcome (U:=Fin q) π d) (M:Fin n→Fin n→ℕ):
    let raw:RawMarkedOutcome (Fin n) (Fin q) Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let t:=startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)
    let J:=z.2;
    ∀(Pack:Finset (Sym2 (Fin n))) (Enew:Fin q→Finset (Sym2 (Fin n)))
      (A:Finset (Fin n×Fin n)) (R:Fin q→Finset (Fin n)),
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
    let K:=MarkedSampleArc P π (3*d) σ true;
    HasResourceDecomposition (markedWheelPhysicalResources (tail:=fun e:E=>e.val.1) (head:=fun e:E=>e.val.2)
      (ktail:=fun e:K=>e.val.1) (khead:=fun e:K=>e.val.2) (m:=r+4) (π:=π) (b:=3*d) (H₀:=H₀) (Hₖ:=HK))
      (markedDecompositionTarget (markedPhysicalRimSet (fun e:E=>e.val.1) (fun e:E=>e.val.2)
        (fun e:K=>e.val.1) (fun e:K=>e.val.2) π) H₀ HK)→
    LongMatchingSameSampleFactorDataByCardinality S P F π d r z M :=by
  intro raw t J Pack Enew A R hprov Small hSmall σ T hcode Y H₀ HK E K hdec
  exact ⟨Pack,Enew,A,R,hprov,Small,hSmall,σ,T,hcode,hdec⟩
end Oberwolfach
