module

public import Oberwolfach.MarkedEncodedFixedReservoirCompletion
public import Oberwolfach.MarkedReservedChangeGraphTransfer
public import Oberwolfach.MarkedReferenceEncodedTerminalAgreement
public import Oberwolfach.MarkedEncodedHostReservedRimTransfer

@[expose] public section

/-! Completion of an encoded later host using a fixed reservoir chosen in
the original sample. The final arc and spoke agreement follows from the
first protected pair and the actual reference chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}

theorem marked_encoded_fixed_reservoir_completion_from_change_graph
    (levels:ℕ→MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (count:ℕ) (hcount:0<count) (gammaLoss sigmaLoss:ℝ):
    letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
    letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
    letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
    letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10;
    ∀ chain:MarkedReferenceLevelChain levels count,
    (∀ i,i<count→MarkedReferenceLevelStepProperty (levels i) gammaLoss sigmaLoss)→
    let V:=(levels 0).VP
    let U:=(levels 0).UP
    let P:=(levels 0).PP
    let π:=(levels 0).πP
    let I:=(levels 0).I
    let J:=(levels 0).J
    let X:=(levels (count-1)).I.image (chain.intoV (count-1))
    let Y:=(levels (count-1)).J.image (chain.intoU (count-1));
    ∀ (Ehost Khost:Type) (tailH headH:Ehost→V) (ktailH kheadH:Khost→V),
    ∀ hpH:Function.Injective (markedPhysicalEdge tailH headH ktailH kheadH π),
    ∀ hEH:∀ e,¬PermutationClose π (3*d) (tailH e) (headH e)∧P.Adj (tailH e) (headH e),
    ∀ hKH:∀ e,¬PermutationClose π (3*d) (ktailH e) (kheadH e)∧P.Adj (ktailH e) (π (kheadH e)),
    ∀ σ:RawMarkedOutcome V U Gamma Color,
    (levels 0).σBase=rawMarkedEncodeHost tailH headH ktailH kheadH π σ I→
    (∀ mark a b,a∈I→b∈I→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark a b=1 ↔
        (if mark then ∃ e:Khost,ktailH e=a∧kheadH e=b else ∃ e:Ehost,tailH e=a∧headH e=b)))→
    ∀ Hold:Bool→V→U→Prop,
    (∀ b v u,v∈I→u∈J→(Hold b v u↔(levels 0).HBase b v u))→
    let Eold:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let Kold:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail₀:=fun e:Eold=>e.val.1
    let head₀:=fun e:Eold=>e.val.2
    let ktail₀:=fun e:Kold=>e.val.1
    let khead₀:=fun e:Kold=>e.val.2
    let Enew:=MarkedSampleArc P π (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) false
    let Knew:=MarkedSampleArc P π (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) true
    let tail:=fun e:Enew=>e.val.1
    let head:=fun e:Enew=>e.val.2
    let ktail:=fun e:Knew=>e.val.1
    let khead:=fun e:Knew=>e.val.2
    let H₀:=(levels 0).HBase false
    let HK:=(levels 0).HBase true
    let A₀:=Finset.univ.filter (fun a:Eold⊕Kold=>Sum.elim tail₀ ktail₀ a∈X∧Sum.elim head₀ khead₀ a∈X)
    let S₀:=Finset.univ.filter (fun z:V×U=>(Hold false z.1 z.2∨Hold true z.1 z.2)∧z.1∈X∧z.2∈Y);
    ∀ C:Finset (Finset V⊕(V×U)),
    (∀ A⊆A₀,∀ S⊆S₀,MarkedRemainderDivisible tail₀ head₀ ktail₀ khead₀ (Hold true) A S (r+4)→
      IsResourceAbsorber
        (fun W:MarkedWheel tail₀ head₀ ktail₀ khead₀ (r+4) π (3*d) (Hold false) (Hold true)=>markedWheelPhysicalResources W)
        (A.image (fun a=>Sum.inl (markedPhysicalEdge tail₀ head₀ ktail₀ khead₀ π a))∪S.image Sum.inr) C)→
    ∀ D:SimpleGraph V,
    (∀ e:Sym2 V,e∈P.edgeFinset→σ (Sum.inl e)≠(levels 0).σBase (Sum.inl e)→e∈D.edgeFinset)→
    (∀ e:Sym2 V,Sum.inl e.toFinset∈C→e∉D.edgeFinset)→
    (∀ b v u,Sum.inr (v,u)∈C→Hold b v u→(levels 0).HBase b v u)→
    (∀ e∈C,¬MarkedOldResource tail₀ head₀ ktail₀ khead₀ π I J e)→
    MarkedRemainderDivisible tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2)) (r+4)→
    (C.card:ℝ)≤gammaLoss*Fintype.card V→(C.card:ℝ)≤sigmaLoss*Fintype.card V→
    let S:=Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2)
    let Full:=markedFiniteResources tail head ktail khead π Finset.univ S;
    HasResourceDecomposition
      (fun W:MarkedWheel tail head ktail khead (r+4) π (3*d) H₀ HK=>markedWheelPhysicalResources W) Full := by
  intro chain hsteps V U P π I J X Y Ehost Khost tailH headH ktailH kheadH hpH hEH hKH σ hσ hAgree Hold hsp
    Eold Kold tail₀ head₀ ktail₀ khead₀ Enew Knew tail head ktail khead H₀ HK A₀ S₀ C habs D hchange havoid hspoke
    hCold hdiv hG hStar S Full
  letI : ∀ i,Fintype (levels i).VP := fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP := fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP := fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP := fun i=>(levels i).inst10
  have hchange':∀ e:Sym2 V,e∈P.edgeFinset→σ (Sum.inl e)≠
      rawMarkedEncodeHost tailH headH ktailH kheadH π σ I (Sum.inl e)→e∈D.edgeFinset:=by
    intro e he hn
    apply hchange e he
    rw [hσ]
    exact hn
  obtain ⟨hOrd,hMark⟩:=marked_reserved_rim_change_graph_transfers P π d tailH headH ktailH kheadH
    hpH hEH hKH σ I (levels 0).hI hAgree C D hchange' havoid
  exact marked_encoded_fixed_reservoir_completion levels count hcount gammaLoss sigmaLoss chain hsteps
    Ehost Khost tailH headH ktailH kheadH hpH hEH hKH σ hσ hAgree Hold hsp C habs hOrd hMark
    (fun v u he hh=>hspoke false v u he hh) (fun v u he hh=>hspoke true v u he hh)
    hCold hdiv hG hStar
end Oberwolfach
