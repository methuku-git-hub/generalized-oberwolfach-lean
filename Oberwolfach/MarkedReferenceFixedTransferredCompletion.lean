module

public import Oberwolfach.MarkedReferenceFiniteIteration
public import Oberwolfach.MarkedReferenceTerminalTransfer
public import Oberwolfach.MarkedReferenceFixedTransferredIteration
public import Oberwolfach.MarkedReservedAbsorberChangedHostDeletion

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

theorem marked_reference_completion_with_fixed_transferred_absorber
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
    HasResourceDecomposition
      (fun W:MarkedWheel tail₀ head₀ ktail₀ khead₀ (r+4) π (3*d) H₀old HKold=>markedWheelPhysicalResources W) C →
    (∀ e∈C,match e with | Sum.inl a=>∃ t:E₀⊕K₀,markedPhysicalEdge tail₀ head₀ ktail₀ khead₀ π t=a | Sum.inr _=>True) →
    (∀ e∈C,¬MarkedOldResource tail₀ head₀ ktail₀ khead₀ π (levels 0).I (levels 0).J e) →
    MarkedRemainderDivisible tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun z:VP×UP=>H₀ z.1 z.2∨HK z.1 z.2)) (r+4) →
    (C.card:ℝ)≤gammaLoss*Fintype.card VP →
    (C.card:ℝ)≤sigmaLoss*Fintype.card VP →
    let S:=Finset.univ.filter (fun z:VP×UP=>H₀ z.1 z.2∨HK z.1 z.2)
    let Full:=markedFiniteResources tail head ktail khead π Finset.univ S;
    HasResourceDecomposition R Full := by
  intro chain hsteps VP UP E K tail head ktail khead H₀ HK π R last X Y
    E₀ K₀ _ _ tail₀ head₀ ktail₀ khead₀ H₀old HKold A₀ S₀ C hp₀ habs hA hS hCE hCK hC₀ hCk
    hCdec hCsupport hCold hdiv hG hStar S Full
  letI : ∀ i,Fintype (levels i).VP := fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP := fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP := fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP := fun i=>(levels i).inst10
  have hEmpty:C.filter (markedInnerResource (levels 0).I (levels 0).J)=∅:=by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨he,hi⟩:=Finset.mem_filter.mp he
    exact hCold e he ((marked_old_resource_iff_inner (levels 0).I (levels 0).J (levels 0).hI e (hCsupport e he)).mpr hi)
  have hCdec':HasResourceDecomposition R C:=
    marked_decomposition_transfer_on_resources C hCE hCK hC₀ hCk hCdec
  obtain ⟨D,hValid,hRemoved,hRemain⟩:=marked_reference_absorber_deletion
    (levels 0).PP π d (r+4) (levels 0).σBase (levels 0).HBase (levels 0).I (levels 0).J
    (gammaLoss*Fintype.card VP) (sigmaLoss*Fintype.card VP)
    (fun v u=>(levels 0).hdtypesBase u v) hdiv C hCdec' hEmpty hG hStar
  let F:=markedResourceEmbedding (chain.intoV 0).toEmbedding (chain.intoU 0)
  have hFid:(F:Finset VP⊕(VP×UP) → Finset VP⊕(VP×UP))=id:=by
    funext z
    cases z with
    | inl a=>
      simp only [F,markedResourceEmbedding,Function.Embedding.sumMap,Function.Embedding.coeFn_mk,Sum.map_inl]
      congr 1
      ext v
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨x,hx,hxv⟩
        change chain.intoV 0 x=v at hxv
        rw [chain.firstV] at hxv
        exact hxv ▸ hx
      · intro hv
        exact ⟨v,hv,chain.firstV v⟩
    | inr a=>
      cases a with
      | mk v u=>
        change Sum.inr ((chain.intoV 0) v,(chain.intoU 0) u)=Sum.inr (v,u)
        rw [chain.firstV,chain.firstU]
  have hImage:(D.remaining (levels 0).HBase).image F=Full\C:=by
    rw [hRemain,hFid,Finset.image_id]
  have hDis:Disjoint C ((D.remaining (levels 0).HBase).image F):=by
    rw [hImage]
    exact Finset.disjoint_left.mpr (fun _ ha hb=>(Finset.mem_sdiff.mp hb).2 ha)
  have hResult:=marked_reference_iteration_with_fixed_transferred_absorber
    levels count hcount gammaLoss sigmaLoss chain hsteps E₀ K₀ tail₀ head₀ ktail₀ khead₀ H₀old HKold
    A₀ S₀ C hp₀ habs hA hS hCE hCK hC₀ hCk D hValid hDis
  have hCsub:C⊆Full:=by
    have hh:=D.removed_subset (levels 0).HBase (r+4) (levels 0).I (levels 0).J
      (gammaLoss*Fintype.card VP) (sigmaLoss*Fintype.card VP) hValid
    simpa only [hRemoved] using hh
  have hUnion:C∪(Full\C)=Full:=by
    ext e
    have hh:=fun he=>hCsub (x:=e) he
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto
  rw [hImage,hUnion] at hResult
  exact hResult

end Oberwolfach
