module

public import Oberwolfach.MarkedReferenceLevelGeometry
public import Oberwolfach.MarkedEncodedHostTerminalAgreement

@[expose] public section

/-! The nested terminal pair lies in the first protected pair, so the
encoded-host agreement supplies all of its typed rim occurrences in the
original sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}

theorem marked_reference_encoded_terminal_arc_agreement
    (levels:ℕ→MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (count:ℕ) (hcount:0<count):
    letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
    letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
    letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
    letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10;
    ∀ chain:MarkedReferenceLevelChain levels count,
    let V:=(levels 0).VP
    let U:=(levels 0).UP
    let P:=(levels 0).PP
    let π:=(levels 0).πP
    let I:=(levels 0).I
    let X:=(levels (count-1)).I.image (chain.intoV (count-1));
    ∀ (E K:Type) (tail head:E→V) (ktail khead:K→V),
      ∀ hp:Function.Injective (markedPhysicalEdge tail head ktail khead π),
      ∀ hE:∀ e,¬PermutationClose π (3*d) (tail e) (head e)∧P.Adj (tail e) (head e),
      ∀ hK:∀ e,¬PermutationClose π (3*d) (ktail e) (khead e)∧P.Adj (ktail e) (π (khead e)),
      ∀ σ:RawMarkedOutcome V U Gamma Color,
      (levels 0).σBase=rawMarkedEncodeHost tail head ktail khead π σ I→
      (∀ mark a b,a∈I→b∈I→
        (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark a b=1 ↔
          (if mark then ∃ e:K,ktail e=a∧khead e=b else ∃ e:E,tail e=a∧head e=b)))→
      let Eold:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
      let Kold:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
      let Enew:=MarkedSampleArc P π (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) false
      let Knew:=MarkedSampleArc P π (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) true
      let srcOld:=Sum.elim (fun e:Eold=>e.val.1) (fun e:Kold=>e.val.1)
      let dstOld:=Sum.elim (fun e:Eold=>e.val.2) (fun e:Kold=>e.val.2)
      let srcNew:=Sum.elim (fun e:Enew=>e.val.1) (fun e:Knew=>e.val.1)
      let dstNew:=Sum.elim (fun e:Enew=>e.val.2) (fun e:Knew=>e.val.2)
      let A₀:=Finset.univ.filter (fun a:Eold⊕Kold=>srcOld a∈X∧dstOld a∈X);
      ∀ a:Enew⊕Knew,srcNew a∈X→dstNew a∈X→
        ∃ a₀∈A₀,srcOld a₀=srcNew a∧dstOld a₀=dstNew a∧markedArcType a₀=markedArcType a := by
  intro chain V U P π I X E K tail head ktail khead hp hE hK σ hσ hAgree
  letI : ∀ i,Fintype (levels i).VP := fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP := fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP := fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP := fun i=>(levels i).inst10
  have hXI:X⊆I:=(marked_reference_terminal_pair_in_first_pair levels chain hcount).1
  rw [hσ]
  exact marked_encoded_host_terminal_arc_agreement P π d tail head ktail khead hp hE hK σ I X hXI (levels 0).hI hAgree

/-- The same nesting supplies the terminal spoke hypothesis from agreement
on the first protected pair. -/
theorem marked_reference_terminal_spoke_agreement
    (levels:ℕ→MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (count:ℕ) (hcount:0<count):
    letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
    letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
    letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
    letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10;
    ∀ chain:MarkedReferenceLevelChain levels count,
    let V:=(levels 0).VP
    let U:=(levels 0).UP
    let I:=(levels 0).I
    let J:=(levels 0).J
    let X:=(levels (count-1)).I.image (chain.intoV (count-1))
    let Y:=(levels (count-1)).J.image (chain.intoU (count-1));
    ∀ Hold:Bool→V→U→Prop,
    (∀ b v u,v∈I→u∈J→(Hold b v u↔(levels 0).HBase b v u))→
    let S₀:=Finset.univ.filter (fun z:V×U=>
      (Hold false z.1 z.2∨Hold true z.1 z.2)∧z.1∈X∧z.2∈Y);
    ∀ z:V×U,z.1∈X→z.2∈Y→((levels 0).HBase false z.1 z.2∨(levels 0).HBase true z.1 z.2)→
      z∈S₀ ∧ (Hold false z.1 z.2↔(levels 0).HBase false z.1 z.2) ∧
        (Hold true z.1 z.2↔(levels 0).HBase true z.1 z.2) := by
  intro chain V U I J X Y Hold hAgree
  letI : ∀ i,Fintype (levels i).VP := fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP := fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP := fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP := fun i=>(levels i).inst10
  obtain ⟨hXI,hYJ⟩:=marked_reference_terminal_pair_in_first_pair levels chain hcount
  exact marked_terminal_spoke_agreement Hold (levels 0).HBase I X J Y hXI hYJ hAgree

end Oberwolfach
