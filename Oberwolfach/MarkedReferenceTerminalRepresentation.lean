module

public import Oberwolfach.MarkedReferenceLevelData

@[expose] public section

/-! The last physical remainder is represented by its actual typed arc and
spoke sets on the final fixed reference. Their four divisibility equations
and containment in the terminal pair are included. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}

def MarkedReferenceTerminalRepresentation
    (level:MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    {V₀ U₀:Type} [DecidableEq V₀] [DecidableEq U₀]
    (f:level.VP↪V₀) (g:level.UP↪U₀) (L:Finset (Finset V₀⊕(V₀×U₀))):Prop:=
  letI : Fintype level.VP:=level.inst7
  letI : Fintype level.UP:=level.inst8
  letI : LinearOrder level.VP:=level.inst9
  letI : DecidableEq level.UP:=level.inst10
  let E:=MarkedSampleArc level.PP level.πP (3*d) (fun e=>level.σBase (Sum.inl e)) false
  let K:=MarkedSampleArc level.PP level.πP (3*d) (fun e=>level.σBase (Sum.inl e)) true
  let S:=Finset.univ.filter (fun z:level.VP×level.UP=>level.HBase false z.1 z.2∨level.HBase true z.1 z.2);
  ∃ AR:Finset (E⊕K),∃ SR:Finset (level.VP×level.UP),SR⊆S ∧
    (∀ a∈AR,Sum.elim (fun e:E=>e.val.1) (fun e:K=>e.val.1) a∈level.I ∧
      Sum.elim (fun e:E=>e.val.2) (fun e:K=>e.val.2) a∈level.I) ∧
    (∀ z∈SR,z.1∈level.I ∧ z.2∈level.J) ∧
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (level.HBase true) AR SR (r+4) ∧
    L=(markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) level.πP AR SR).image (markedResourceEmbedding f g)

end Oberwolfach
