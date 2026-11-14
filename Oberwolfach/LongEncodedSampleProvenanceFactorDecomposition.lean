module

public import Oberwolfach.LongFactorProvenanceMarkedDecomposition
public import Oberwolfach.LongEncodedResidualSampleReconstructionGeometry

@[expose] public section
/-! A decomposition of the actual corrected sample reconstructs the original
factors on the protected class, using the same selected complement data. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance encodedSampleFactorFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem long_encoded_sample_provenance_factor_decomposition
    {n D:ℕ} [Nonempty (Fin n)] (hEven:Even D) (S P:SimpleGraph (Fin n)) (hS:S.IsRegularOfDegree D)
    (F:Fin (D/2)→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d m b:ℕ) (hd:2≤d) (hb:1≤b)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (raw:RawMarkedOutcome (Fin n) (Fin (D/2)) Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (Pack:Finset (Sym2 (Fin n))) (Enew:Fin (D/2)→Finset (Sym2 (Fin n)))
    (A:Finset (Fin n×Fin n)) (R:Fin (D/2)→Finset (Fin n))
    (hprov:LongFactorComplementProvenance F S P π d m raw t J Pack Enew A R)
    (Small:SimpleGraph (Fin n)) (hSmall:Small.edgeFinset=A.image (fun a=>s(a.1,a.2)))
    (M:Fin n→Fin n→ℕ) (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (σ:Sym2 (Fin n)→Option (Bool×Bool))
    (T:Finset {a:Fin n×Fin n // longEligibleResidualArc M Small ⊥ a})
    (hcode:∀mark x y,markedPhysicalRim P π (3*d) σ mark x y=1 ↔
      if mark then ∃e:residualMarkedArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧π.symm e.val.val.2=y
      else ∃e:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧e.val.val.2=y):
    let Y:=fun u=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J u=>d) Subtype.val
    let H₀:=fun v u=>v∈R u\Y u
    let HK:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false true true
    let E:=MarkedSampleArc P π (3*d) σ false
    let K:=MarkedSampleArc P π (3*d) σ true;
    HasResourceDecomposition (markedWheelPhysicalResources (tail:=fun e:E=>e.val.1) (head:=fun e:E=>e.val.2)
      (ktail:=fun e:K=>e.val.1) (khead:=fun e:K=>e.val.2) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK))
      (markedDecompositionTarget (markedPhysicalRimSet (fun e:E=>e.val.1) (fun e:E=>e.val.2)
        (fun e:K=>e.val.1) (fun e:K=>e.val.2) π) H₀ HK) →
    HasFactorDecomposition S F :=by
  intro Y H₀ HK E K hdec
  have hh:=long_encoded_residual_sample_reconstruction_geometry P S Small M hphysical π d σ T hcode
  exact long_factor_provenance_marked_decomposition hEven S P hS F hF π d m b hd hb hnoshort raw t J Pack Enew A R hprov Small hSmall
    E K (fun e=>e.val.1) (fun e=>e.val.2) (fun e=>e.val.1) (fun e=>e.val.2) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2 hdec
end Oberwolfach
