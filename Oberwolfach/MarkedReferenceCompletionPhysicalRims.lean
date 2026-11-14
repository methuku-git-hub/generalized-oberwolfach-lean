module

public import Oberwolfach.MarkedReservedPropertyPhysicalCongruence
public import Oberwolfach.MarkedReferenceReservedCompletion
public import Oberwolfach.MarkedSampledReservedAbsorbersAfterPhysicalDeletion
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

theorem marked_reference_completion_after_physical_deletion_physical_rims
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
    ∀ (σOriginal:RawMarkedOutcome VP UP Gamma Color) (HOriginal:Bool→VP→UP→Prop)
      (ζ:ℝ) (DR:SimpleGraph VP) (DS:SimpleGraph (VP⊕UP)),
    (∀ mark x y,markedPhysicalRim (levels 0).PP (levels 0).πP (3*d)
      (fun e=>(levels 0).σBase (Sum.inl e)) mark x y=
      markedPhysicalRim (levels 0).PP (levels 0).πP (3*d)
      (fun e=>rawMarkedDeleteRims σOriginal DR.edgeFinset (Sum.inl e)) mark x y) →
    (levels 0).HBase=markedDeletePhysicalSpokes HOriginal DS →
    (∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card VP) → (∀ z,(DS.degree z:ℝ)≤ζ*Fintype.card VP) →
    (∀ (DR':SimpleGraph VP) (DS':SimpleGraph (VP⊕UP)),
      (∀ x,(DR'.degree x:ℝ)≤ζ*Fintype.card VP) → (∀ z,(DS'.degree z:ℝ)≤ζ*Fintype.card VP) →
      let σ':=rawMarkedDeleteRims σOriginal DR'.edgeFinset
      let H':=markedDeletePhysicalSpokes HOriginal DS'
      let E':=MarkedSampleArc (levels 0).PP π (3*d) (fun e=>σ' (Sum.inl e)) false
      let K':=MarkedSampleArc (levels 0).PP π (3*d) (fun e=>σ' (Sum.inl e)) true;
      MarkedReservedTerminalAbsorberProperty (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) r s a₀ b₀ e₀ f ε) →
    MarkedRemainderDivisible tail head ktail khead HK Finset.univ S (r+4) →
    X.card+Y.card≤s →
    ((levels 0).I.card:ℝ)≤ε*Fintype.card VP+f →
    ((levels 0).J.card:ℝ)≤ε*Fintype.card VP+f →
    (e₀:ℝ)≤gammaLoss*Fintype.card VP → (e₀:ℝ)≤sigmaLoss*Fintype.card VP →
    ∀ F₀:Finset (Finset VP⊕(VP×UP)),F₀.card≤f →
    HasResourceDecomposition R Full := by
  intro chain hsteps VP UP E K tail head ktail khead H₀ HK π R S Full last X Y
    σOriginal HOriginal ζ DR DS hσ hH hrim hspoke hrob hdiv hs hI hJ hG hStar F₀ hF
  letI : ∀ i,Fintype (levels i).VP := fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP := fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP := fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP := fun i=>(levels i).inst10
  have habs:=hrob DR DS hrim hspoke
  have habs':MarkedReservedTerminalAbsorberProperty tail head ktail khead H₀ HK π (3*d) r s a₀ b₀ e₀ f ε:=by
    dsimp only [tail,head,ktail,khead,H₀,HK,E,K,π]
    rw [hH]
    apply marked_reserved_property_physical_congruence (levels 0).PP (levels 0).πP (3*d) r s a₀ b₀ e₀ f ε
      (fun e=>rawMarkedDeleteRims σOriginal DR.edgeFinset (Sum.inl e))
      (fun e=>(levels 0).σBase (Sum.inl e))
      (markedDeletePhysicalSpokes HOriginal DS false) (markedDeletePhysicalSpokes HOriginal DS true)
    · intro mark x y;exact (hσ mark x y).symm
    · exact habs
  exact marked_reference_reserved_completion levels count hcount gammaLoss sigmaLoss ε s a₀ b₀ e₀ f
    chain hsteps habs' hdiv hs hI hJ hG hStar F₀ hF

end Oberwolfach
