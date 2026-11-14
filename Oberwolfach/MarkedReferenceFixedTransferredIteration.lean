module

public import Oberwolfach.MarkedReferenceFiniteIteration
public import Oberwolfach.MarkedReferenceTerminalTransfer
public import Oberwolfach.MarkedTerminalRemainderHostTransfer

@[expose] public section

/-! Iterate from a fixed reservoir chosen in another typed host. Only the
terminal remainder and the reservoir resources need compatible typed
representations; the modified host may have additional resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}

theorem marked_reference_iteration_with_fixed_transferred_absorber
    (levels:ℕ → MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (count:ℕ) (hcount:0<count) (gammaLoss sigmaLoss:ℝ):
    letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
    letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
    letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
    letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10;
    ∀ chain:MarkedReferenceLevelChain levels count,
    (∀ i,i<count → MarkedReferenceLevelStepProperty (levels i) gammaLoss sigmaLoss) →
    let VP:=(levels 0).VP
    let UP:=(levels 0).UP
    let E:=MarkedSampleArc (levels 0).PP (levels 0).πP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) false
    let K:=MarkedSampleArc (levels 0).PP (levels 0).πP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let H₀:=(levels 0).HBase false
    let HK:=(levels 0).HBase true
    let π:=(levels 0).πP
    let R:=fun W:MarkedWheel tail head ktail khead (r+4) π (3*d) H₀ HK=>markedWheelPhysicalResources W
    let last:=count-1
    let X:=(levels last).I.image (chain.intoV last)
    let Y:=(levels last).J.image (chain.intoU last);
    ∀ (E₀ K₀:Type) [DecidableEq E₀] [DecidableEq K₀]
      (tail₀ head₀:E₀→VP) (ktail₀ khead₀:K₀→VP) (H₀old HKold:VP→UP→Prop)
      (A₀:Finset (E₀⊕K₀)) (S₀:Finset (VP×UP)) (C:Finset (Finset VP⊕(VP×UP))),
    Function.Injective (markedPhysicalEdge tail₀ head₀ ktail₀ khead₀ π) →
    (∀ A⊆A₀,∀ S⊆S₀,MarkedRemainderDivisible tail₀ head₀ ktail₀ khead₀ HKold A S (r+4)→
      IsResourceAbsorber
        (fun W:MarkedWheel tail₀ head₀ ktail₀ khead₀ (r+4) π (3*d) H₀old HKold=>markedWheelPhysicalResources W)
        (A.image (fun a=>Sum.inl (markedPhysicalEdge tail₀ head₀ ktail₀ khead₀ π a))∪S.image Sum.inr) C) →
    (∀ a:E⊕K,Sum.elim tail ktail a∈X→Sum.elim head khead a∈X→
      ∃ a₀∈A₀,Sum.elim tail₀ ktail₀ a₀=Sum.elim tail ktail a∧
        Sum.elim head₀ khead₀ a₀=Sum.elim head khead a∧markedArcType a₀=markedArcType a) →
    (∀ z:VP×UP,z.1∈X→z.2∈Y→(H₀ z.1 z.2∨HK z.1 z.2)→
      z∈S₀ ∧ (H₀old z.1 z.2↔H₀ z.1 z.2) ∧ (HKold z.1 z.2↔HK z.1 z.2)) →
    (∀ e:E₀,Sum.inl ({tail₀ e,head₀ e}:Finset VP)∈C→∃ e':E,tail e'=tail₀ e∧head e'=head₀ e) →
    (∀ e:K₀,Sum.inl ({ktail₀ e,π (khead₀ e)}:Finset VP)∈C→∃ e':K,ktail e'=ktail₀ e∧khead e'=khead₀ e) →
    (∀ v u,Sum.inr (v,u)∈C→H₀old v u→H₀ v u) →
    (∀ v u,Sum.inr (v,u)∈C→HKold v u→HK v u) →
    ∀ D₀:MarkedReferenceDeletion (levels 0).PP π d (levels 0).σBase,
      D₀.Valid (levels 0).HBase (r+4) (levels 0).I (levels 0).J
        (gammaLoss*Fintype.card VP) (sigmaLoss*Fintype.card VP) →
      let B:=(D₀.remaining (levels 0).HBase).image (markedResourceEmbedding (chain.intoV 0).toEmbedding (chain.intoU 0));
      Disjoint C B → HasResourceDecomposition R (C∪B) := by
  intro chain hsteps VP UP E K tail head ktail khead H₀ HK π R last X Y
    E₀ K₀ _ _ tail₀ head₀ ktail₀ khead₀ H₀old HKold A₀ S₀ C hp₀ habs hA hS hCE hCK hC₀ hCk D₀ hD₀ B hCB
  letI : ∀ i,Fintype (levels i).VP := fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP := fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP := fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP := fun i=>(levels i).inst10
  obtain ⟨L,hLB,hdec,hInner,hRep⟩:=marked_reference_finite_iteration levels count hcount gammaLoss sigmaLoss chain hsteps D₀ hD₀
  have hlast:last<count := by dsimp only [last];omega
  have hglobal:=marked_reference_terminal_transfer levels chain last hlast L hRep
  unfold MarkedAmbientTerminalRepresentation at hglobal
  dsimp only at hglobal
  obtain ⟨A,S,hS',hAX,hSY,hdiv,hL⟩:=hglobal
  have hSS:S⊆S₀:=by
    intro z hz
    exact (hS z (hSY z hz).1 (hSY z hz).2 (Finset.mem_filter.mp (hS' hz)).2).1
  have hST:∀ z∈S,(H₀old z.1 z.2↔H₀ z.1 z.2)∧(HKold z.1 z.2↔HK z.1 z.2):=by
    intro z hz
    exact (hS z (hSY z hz).1 (hSY z hz).2 (Finset.mem_filter.mp (hS' hz)).2).2
  have hp:=markedSampleArc_physical_injective (levels 0).PP π (3*d) (fun a=>(levels 0).σBase (Sum.inl a))
  have hAbs:=marked_terminal_remainder_absorption_between_hosts hp₀ hp A₀ A S C
    (fun A' hA' hd=>habs A' hA' S hSS hd) hdiv
    (fun a ha=>hA a (hAX a ha).1 (hAX a ha).2) hST hCE hCK hC₀ hCk
  have hAbsDec:HasResourceDecomposition R (C∪L):=by
    rw [hL]
    exact hAbs.2.2
  have hdis:Disjoint (B\L) (C∪L):=by
    apply Finset.disjoint_union_right.mpr
    exact ⟨hCB.symm.mono_left Finset.sdiff_subset,
      Finset.disjoint_left.mpr (fun _ he hf=>(Finset.mem_sdiff.mp he).2 hf)⟩
  have hwhole:=resource_decomposition_union R _ _ hdec hAbsDec hdis
  have heq:(B\L)∪(C∪L)=C∪B:=by
    ext e
    have hh:=fun he=>hLB (x:=e) he
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto
  rwa [heq] at hwhole

end Oberwolfach
