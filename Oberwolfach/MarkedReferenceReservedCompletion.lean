module

public import Oberwolfach.MarkedReferenceReservedIteration
public import Oberwolfach.MarkedReferenceAbsorberDeletion
public import Oberwolfach.MarkedReferenceLevelGeometry
public import Oberwolfach.MarkedOldInnerAgreement

@[expose] public section

/-! Complete a fixed reference host using the reserved terminal absorber.
The initial state is constructed by deleting its actual wheel decomposition;
its divisibility and both loss bounds are not independent hypotheses. -/
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

theorem marked_reference_reserved_completion
    (levels:ℕ → MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (count:ℕ) (hcount:0<count) (gammaLoss sigmaLoss ε:ℝ) (s a₀ b₀ e₀ f:ℕ):
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
    let S:=Finset.univ.filter (fun z:VP×UP=>H₀ z.1 z.2∨HK z.1 z.2)
    let Full:=markedFiniteResources tail head ktail khead π Finset.univ S
    let last:=count-1
    let X:=(levels last).I.image (chain.intoV last)
    let Y:=(levels last).J.image (chain.intoU last);
    MarkedReservedTerminalAbsorberProperty tail head ktail khead H₀ HK π (3*d) r s a₀ b₀ e₀ f ε →
    MarkedRemainderDivisible tail head ktail khead HK Finset.univ S (r+4) →
    X.card+Y.card≤s →
    ((levels 0).I.card:ℝ)≤ε*Fintype.card VP+f →
    ((levels 0).J.card:ℝ)≤ε*Fintype.card VP+f →
    (e₀:ℝ)≤gammaLoss*Fintype.card VP → (e₀:ℝ)≤sigmaLoss*Fintype.card VP →
    ∀ F₀:Finset (Finset VP⊕(VP×UP)),F₀.card≤f →
    HasResourceDecomposition R Full := by
  intro chain hsteps VP UP E K tail head ktail khead H₀ HK π R S Full last X Y habs hdiv hs hI hJ hG hStar F₀ hF
  letI : ∀ i,Fintype (levels i).VP := fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP := fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP := fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP := fun i=>(levels i).inst10
  obtain ⟨hXI,hYJ⟩:=marked_reference_terminal_pair_in_first_pair levels chain hcount
  obtain ⟨C,hCF,hCe,hCr,hCu,hCold,hCdec,hComplete⟩:=marked_reference_reserved_iteration
    levels count hcount gammaLoss sigmaLoss ε s a₀ b₀ e₀ f chain hsteps habs hs
    (levels 0).I (levels 0).J hXI hYJ hI hJ F₀ hF
  have hEmpty:C.edges.filter (markedInnerResource (levels 0).I (levels 0).J)=∅:=
    marked_reserved_absorber_avoids_inner C (levels 0).I (levels 0).J (levels 0).hI hCold
  have hCG:(C.edges.card:ℝ)≤gammaLoss*Fintype.card VP:=by
    exact (show (C.edges.card:ℝ)≤e₀ by exact_mod_cast hCe).trans hG
  have hCS:(C.edges.card:ℝ)≤sigmaLoss*Fintype.card VP:=by
    exact (show (C.edges.card:ℝ)≤e₀ by exact_mod_cast hCe).trans hStar
  have htypes:∀ v u,¬(H₀ v u∧HK v u):=fun v u=>(levels 0).hdtypesBase u v
  obtain ⟨D,hValid,hRemoved,hRemain⟩:=marked_reference_absorber_deletion
    (levels 0).PP π d (r+4) (levels 0).σBase (levels 0).HBase (levels 0).I (levels 0).J
    (gammaLoss*Fintype.card VP) (sigmaLoss*Fintype.card VP) htypes hdiv C.edges hCdec hEmpty hCG hCS
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
  have hImage:(D.remaining (levels 0).HBase).image F=Full\C.edges:=by
    rw [hRemain,hFid,Finset.image_id]
  have hDis:Disjoint C.edges ((D.remaining (levels 0).HBase).image F):=by
    rw [hImage]
    exact Finset.disjoint_left.mpr (fun _ ha hb=>(Finset.mem_sdiff.mp hb).2 ha)
  have hResult:=hComplete D hValid hDis
  have hCsub:C.edges⊆Full:=by
    have hh:=D.removed_subset (levels 0).HBase (r+4) (levels 0).I (levels 0).J
      (gammaLoss*Fintype.card VP) (sigmaLoss*Fintype.card VP) hValid
    simpa only [hRemoved] using hh
  have hUnion:C.edges∪(Full\C.edges)=Full:=by
    ext e
    have hh:=fun he=>hCsub (x:=e) he
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto
  rw [hImage,hUnion] at hResult
  exact hResult

end Oberwolfach
