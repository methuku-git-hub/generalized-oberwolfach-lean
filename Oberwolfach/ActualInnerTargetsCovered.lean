module

public import Oberwolfach.InnerRequiredTargets
public import Oberwolfach.ResidualActualData

@[expose] public section
/-! The complement embedding covers every required inner target for the
same old image and residual embedding. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_inner_targets_covered_by_complement
    {X V I:Type} [Fintype X] [Fintype V] [Fintype I]
    [DecidableEq X] [DecidableEq V] [DecidableEq I]
    (K J:I→Type) [∀w,DecidableEq (K w)] [∀w,DecidableEq (J w)]
    (F:I→SimpleGraph X) (data:∀w,ActualResidualData (K:=K w) (J:=J w) (F w))
    (D:I→Finset X) (ψ:I→X→V)
    (fC:∀w,{x // x∉D w}↪V) (Φ:∀w,{x // x∈(data w).remaining}→V)
    (hDR:∀w,Disjoint (D w) (data w).remaining)
    (hold:∀w (x:{x // x∉D w}),x.val∈(data w).oldDomain→fC w x=ψ w x.val)
    (hnew:∀w (x:{x // x∈(data w).remaining}) (hx:x.val∉D w),fC w ⟨x.val,hx⟩=Φ w x)
    (H:Finset I) (A:Finset V) (reserved selected absorber:I→Finset V):
    let occupied:=fun w=>((data w).oldDomain\D w).image (ψ w)
    let Z:=innerRequiredTargets H A reserved selected absorber occupied
    (∀w v,v∈Z w→∃x,Φ w x=v)→
    ∀w∈H,A⊆reserved w∪selected w∪absorber w∪Finset.univ.image (fC w):=by
  intro occupied Z hZ w hw v hv
  by_cases hmem:v∈reserved w∪selected w∪absorber w
  · exact Finset.mem_union_left _ hmem
  · apply Finset.mem_union_right
    by_cases hOcc:v∈occupied w
    · obtain ⟨x,hx,hxv⟩:=Finset.mem_image.mp hOcc
      have hxOld: x∈(data w).oldDomain:=(Finset.mem_sdiff.mp hx).1
      have hxD:x∉D w:=(Finset.mem_sdiff.mp hx).2
      exact Finset.mem_image.mpr ⟨⟨x,hxD⟩,Finset.mem_univ _,(hold w ⟨x,hxD⟩ hxOld).trans hxv⟩
    · have hvZ:v∈Z w:=by
        simp only [Z,innerRequiredTargets,hw,if_true,Finset.mem_sdiff,Finset.mem_union]
        refine ⟨hv,?_⟩
        intro hh
        rcases hh with hh|hh
        · exact hmem (by simpa only [Finset.mem_union] using hh)
        · exact hOcc hh
      obtain ⟨x,hx⟩:=hZ w v hvZ
      have hxD:x.val∉D w:=by intro h;exact Finset.disjoint_left.mp (hDR w) h x.property
      exact Finset.mem_image.mpr ⟨⟨x.val,hxD⟩,Finset.mem_univ _,(hnew w x hxD).trans hx⟩
end Oberwolfach
