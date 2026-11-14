module

public import Oberwolfach.ActualResidualReservedSpokes

@[expose] public section
/-! The assigned remainder anchors avoid the reserved labels if their three
actual sources—the old prescribed images, matching endpoints, and required
inner labels—avoid those labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I K J V:Type} [Fintype I] [DecidableEq I] [DecidableEq K] [DecidableEq J]
  [Fintype V] [DecidableEq V] {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem actual_residual_listed_anchors_avoid_reserved_labels
    (F:∀i,SimpleGraph (X i)) (hF:∀i,(F i).IsRegularOfDegree 2)
    (a:∀i,ActualResidualData (K:=K) (J:=J) (F i))
    (ψ:∀i,X i→V) (hψ:∀i,Set.InjOn (ψ i) (↑(a i).oldDomain:Set (X i)))
    (g:∀i,{x // x∈(a i).remaining}→V)
    (Anchors:∀i,Finset {x // x∈(a i).remaining})
    (Endpoints Required A:I→Finset V) (Kbad:SimpleGraph V) (Lbad:Sym2 V→Finset I)
    (hImages:∀i,(Anchors i).image (g i)=
      (residualSubtypeSet (a i).remaining (a i).prescribed).image (fun x=>ψ i x.1)∪Endpoints i∪Required i)
    (hEnd:∀i v,v∈Endpoints i → ∃e∈Kbad.edgeFinset,v∈e.toFinset ∧ i∈Lbad e)
    (hList:∀e∈Kbad.edgeFinset,∀v∈e.toFinset,∀i∈Lbad e,v∉A i)
    (hRequired:∀i,Disjoint (Required i) (A i))
    (hOld:∀i x,x∈(a i).oldDomain → ψ i x∉A i):
    ∀i x,x∈Anchors i → g i x∉A i :=by
  intro i x hx hA
  have him:g i x∈(Anchors i).image (g i):=Finset.mem_image.mpr ⟨x,hx,rfl⟩
  rw [hImages i] at him
  rcases Finset.mem_union.mp him with hPrev|hReq
  · rcases Finset.mem_union.mp hPrev with hOldIm|hEndIm
    · obtain ⟨y,hy,heq⟩:=Finset.mem_image.mp hOldIm
      have hOldDomain:y.1∈(a i).oldDomain:=
        (residual_subtype_glue_inputs (a i).remaining (a i).prescribed (a i).oldDomain
          ((a i).graph_facts (hF i)).2.2.2.2.2 (ψ i) (hψ i)).1 y |>.mp hy
      have hh:=hOld i y.1 hOldDomain
      rw [heq] at hh
      exact hh hA
    · obtain ⟨e,he,hv,hi⟩:=hEnd i (g i x) hEndIm
      exact hList e he (g i x) hv i hi hA
  · exact (Finset.disjoint_left.mp (hRequired i)) hReq hA
end Oberwolfach
