module

public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! Identify the active set inside a vortex subtype with the corresponding
physical difference set, without changing any vertex or hub. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

def markedVortexActiveVertexEquiv (i:ℕ):
    ↥((↑(Finset.univ\markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) ≃
    ↥((↑(Q.extendedVertices i\Q.extendedVertices (i+1)):Set V)) where
  toFun x:=⟨x.val.val,by
    have hx: x.val∉markedVortexInnerVertices Q i:=(Finset.mem_sdiff.mp x.property).2
    have hnot:x.val.val∉Q.extendedVertices (i+1):=by simpa [markedVortexInnerVertices] using hx
    exact Finset.mem_sdiff.mpr ⟨x.val.property,hnot⟩⟩
  invFun x:=⟨⟨x.val,(Finset.mem_sdiff.mp x.property).1⟩,by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simpa [markedVortexInnerVertices] using (Finset.mem_sdiff.mp x.property).2⟩
  left_inv x:=by apply Subtype.ext;apply Subtype.ext;rfl
  right_inv x:=by apply Subtype.ext;rfl

def markedVortexActiveHubEquiv (i:ℕ):
    ↥((↑(Finset.univ\markedVortexInnerHubs Q i):Set (markedVortexHubType Q i))) ≃
    ↥((↑(Q.extendedIndices i\Q.extendedIndices (i+1)):Set U)) where
  toFun x:=⟨x.val.val,by
    have hx: x.val∉markedVortexInnerHubs Q i:=(Finset.mem_sdiff.mp x.property).2
    have hnot:x.val.val∉Q.extendedIndices (i+1):=by simpa [markedVortexInnerHubs] using hx
    exact Finset.mem_sdiff.mpr ⟨x.val.property,hnot⟩⟩
  invFun x:=⟨⟨x.val,(Finset.mem_sdiff.mp x.property).1⟩,by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simpa [markedVortexInnerHubs] using (Finset.mem_sdiff.mp x.property).2⟩
  left_inv x:=by apply Subtype.ext;apply Subtype.ext;rfl
  right_inv x:=by apply Subtype.ext;rfl

end Oberwolfach
