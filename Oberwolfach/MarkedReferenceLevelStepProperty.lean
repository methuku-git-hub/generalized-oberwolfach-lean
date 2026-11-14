module

public import Oberwolfach.MarkedReferenceLevelData

@[expose] public section

/-! The conclusion needed for iteration at one level: a packing constructed
in the current reference host, exact decomposition of the discarded part,
and a bounded divisible state on every compatible next reference. This is a
predicate on the explicit graph/profile data, not an axiom or an assertion
that these inputs hold for the sampled vortex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}

def MarkedReferenceLevelStepProperty
    (level:MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (gammaLoss sigmaLoss:ℝ):Prop:=
  let VP:=level.VP
  let UP:=level.UP
  letI : Fintype VP:=level.inst7
  letI : Fintype UP:=level.inst8
  letI : LinearOrder VP:=level.inst9
  letI : DecidableEq UP:=level.inst10
  let P:=level.PP
  let π:=level.πP
  let σ:=level.σBase
  let H:=level.HBase
  let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
  let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true;
  ∀ D:MarkedReferenceDeletion P π d σ,
    D.Valid H (r+4) level.I level.J (gammaLoss*Fintype.card VP) (sigmaLoss*Fintype.card VP) →
    let S:=Finset.univ.filter (fun z:VP×UP=>H false z.1 z.2∨H true z.1 z.2)
    let Full:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π Finset.univ S;
    ∃ L:Finset (Finset VP⊕(VP×UP)),L⊆D.remaining H ∧
      L⊆Full.filter (markedInnerResource level.I level.J) ∧
      (∃ AR:Finset (E⊕K),∃ SR:Finset (VP×UP), SR⊆S ∧
        (∀ a∈AR,Sum.elim (fun e:E=>e.val.1) (fun e:K=>e.val.1) a∈level.I ∧
          Sum.elim (fun e:E=>e.val.2) (fun e:K=>e.val.2) a∈level.I) ∧
        (∀ z∈SR,z.1∈level.I ∧ z.2∈level.J) ∧
        MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
          (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) AR SR (r+4) ∧
        L=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
          (fun e:K=>e.val.1) (fun e=>e.val.2) π AR SR) ∧
      HasResourceDecomposition
        (fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
          (fun e:K=>e.val.1) (fun e=>e.val.2) (r+4) π (3*d) (H false) (H true)=>markedWheelPhysicalResources W)
        (D.remaining H\L) ∧
      ∀ (WNext ZNext:Type) [Fintype WNext] [Fintype ZNext] [LinearOrder WNext] [DecidableEq ZNext]
        (fNext:WNext↪oVP) (gNext:ZNext↪UP) (πNext:Equiv.Perm WNext),
        (∀ x,fNext (πNext x)=π (fNext x)) →
        Finset.univ.image fNext=level.I → Finset.univ.image gNext=level.J →
        ∀ (XNext:Finset WNext) (YNext:Finset ZNext),
        (∀ x,fNext x∈level.T↔x∈XNext) → (∀ u,gNext u∈level.Wrem↔u∈YNext) →
        let σ₀:=rawMarkedRestrictPair fNext gNext σ
        let H₀:=fun b x u=>H b (fNext x) (gNext u);
        ∃ Next:MarkedReferenceDeletion (P.comap fNext) πNext d σ₀,
          Next.Valid H₀ (r+4) XNext YNext (gammaLoss*level.I.card) (sigmaLoss*level.I.card) ∧
          (Next.remaining H₀).image (markedResourceEmbedding fNext.toEmbedding gNext)=L

end Oberwolfach
