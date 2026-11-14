module

public import Oberwolfach.MarkedReferenceLevelData

@[expose] public section

/-! A divisible terminal remainder represented in the original reference
host, with its typed endpoints inside the prescribed terminal pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}

def MarkedAmbientTerminalRepresentation
    (level:MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (X:Finset level.VP) (Y:Finset level.UP) (L:Finset (Finset level.VP⊕(level.VP×level.UP))):Prop:=
  letI : Fintype level.VP:=level.inst7
  letI : Fintype level.UP:=level.inst8
  letI : LinearOrder level.VP:=level.inst9
  letI : DecidableEq level.UP:=level.inst10
  let E:=MarkedSampleArc level.PP level.πP (3*d) (fun e=>level.σBase (Sum.inl e)) false
  let K:=MarkedSampleArc level.PP level.πP (3*d) (fun e=>level.σBase (Sum.inl e)) true
  let S₀:=Finset.univ.filter (fun z:level.VP×level.UP=>level.HBase false z.1 z.2∨level.HBase true z.1 z.2);
  ∃ A:Finset (E⊕K),∃ S:Finset (level.VP×level.UP),S⊆S₀ ∧
    (∀ a∈A,Sum.elim (fun e:E=>e.val.1) (fun e:K=>e.val.1) a∈X ∧
      Sum.elim (fun e:E=>e.val.2) (fun e:K=>e.val.2) a∈X) ∧
    (∀ z∈S,z.1∈X∧z.2∈Y) ∧
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (level.HBase true) A S (r+4) ∧
    L=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) level.πP A S

end Oberwolfach
