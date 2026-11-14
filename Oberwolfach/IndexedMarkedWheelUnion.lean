module

public import Oberwolfach.IndexedMarkedWheelExtension

@[expose] public section

/-! An explicit disjoint union of canonical marked wheels, without host
assumptions. Its marked spoke occurrences are in bijection with its hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I:Type} [Fintype I] [DecidableEq I]

def emptyIndexedMarkedGraph:IndexedMarkedGraph Empty Empty Empty Empty:=
  ⟨Empty.elim,Empty.elim,Empty.elim,Empty.elim,Empty.elim,Empty.elim⟩

theorem emptyIndexedMarkedGraph_balanced (m:ℕ):emptyIndexedMarkedGraph.IsBalanced m:=by
  constructor <;> intro v <;> cases v

def indexedMarkedWheelUnion (I:Type) (m:ℕ):
    IndexedMarkedGraph (I×Fin (m+1)) I (Empty⊕(I×Fin (m+1))) (Empty⊕(I×Fin (m+1))):=
  (indexedMarkedWheelExtension emptyIndexedMarkedGraph m).map (Sum.elim Empty.elim id) (Sum.elim Empty.elim id)

theorem indexedMarkedWheelUnion_balanced (m:ℕ):(indexedMarkedWheelUnion I m).IsBalanced m:=
  IndexedMarkedGraph.map_balanced _ m
    (indexedMarkedWheelExtension_balanced emptyIndexedMarkedGraph m (emptyIndexedMarkedGraph_balanced m)) _ _

theorem indexedMarkedWheelUnion_marked_spoke_count (m:ℕ):
    Fintype.card {s:Empty⊕(I×Fin (m+1)) // (indexedMarkedWheelUnion I m).js s=true}=Fintype.card I:=by
  apply Fintype.card_congr
  refine {
    toFun:=fun s=>s.val.elim Empty.elim Prod.fst
    invFun:=fun i=>⟨Sum.inr (i,0),by simp [indexedMarkedWheelUnion,indexedMarkedWheelExtension,
      IndexedMarkedGraph.map,paddingSpokeType]⟩
    left_inv:=?_
    right_inv:=fun _=>rfl}
  rintro ⟨s,hs⟩
  rcases s with e|⟨i,k⟩
  · cases e
  · have hk:k=0:=of_decide_eq_true hs
    apply Subtype.ext
    simp only [Sum.elim_inr,hk]

@[simp] theorem indexedMarkedWheelUnion_src (m:ℕ) (i:I) (k:Fin (m+1)):
    (indexedMarkedWheelUnion I m).src (Sum.inr (i,k))=(i,k):=rfl
@[simp] theorem indexedMarkedWheelUnion_dst (m:ℕ) (i:I) (k:Fin (m+1)):
    (indexedMarkedWheelUnion I m).dst (Sum.inr (i,k))=(i,finRotate (m+1) k):=rfl
@[simp] theorem indexedMarkedWheelUnion_row (m:ℕ) (i:I) (k:Fin (m+1)):
    (indexedMarkedWheelUnion I m).row (Sum.inr (i,k))=(i,k):=rfl
@[simp] theorem indexedMarkedWheelUnion_hub (m:ℕ) (i:I) (k:Fin (m+1)):
    (indexedMarkedWheelUnion I m).hub (Sum.inr (i,k))=i:=rfl

end Oberwolfach
