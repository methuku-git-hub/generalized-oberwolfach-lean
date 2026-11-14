module

public import Oberwolfach.OrdinaryTransferCycleEmbedding

@[expose] public section
/-! Supported labelled transfers descend to induced vertex and hub domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryInducedTransfer (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (r:ℕ) (hr:3≤r) (v:A) (u u':B)
    (C:{C:OrdinaryTransferConfiguration hr Q F H v.val u.val u'.val // Set.range C.labels⊆A}):
    OrdinaryTransferConfiguration hr (Q.induce (A:Set V)) (F.induce (A:Set V))
      (fun (z:A) (h:B)=>H z.val h.val) v u u' :=by
  let f:(Fin r×Fin r)↪A:=⟨fun i=>⟨C.val.labels i,C.property ⟨i,rfl⟩⟩,
    by intro i j hij;exact C.val.labels.injective (congrArg Subtype.val hij)⟩
  let φ:A↪V:=Function.Embedding.subtype (fun z=>z∈(A:Set V))
  have hcomp:f.trans φ=C.val.labels:=by ext i;rfl
  have hv:v∉Set.range f:=by
    rintro ⟨i,hi⟩
    apply C.val.omitted
    exact ⟨i,congrArg Subtype.val hi⟩
  have hv':φ v∉Set.range (f.trans φ):=by rw [hcomp];exact C.val.omitted
  refine ⟨f,hv,?_,?_,?_⟩
  · intro j a b hab
    have hh:((transferCycleGraph (by omega) f v hv j).map φ).Adj (φ a) (φ b):=
      SimpleGraph.map_adj_apply.mpr hab
    rw [transfer_cycle_graph_embedding (by omega) f v hv φ hv' j] at hh
    change (transferCycleGraph (by omega) C.val.labels v.val C.val.omitted j).Adj a.val b.val at hh
    exact C.val.rim_edges j hh
  · intro z hz
    have hz':z.val∈insert v.val (Set.range C.val.labels):=by
      rcases Set.mem_insert_iff.mp hz with he|⟨i,hi⟩
      · left;exact congrArg Subtype.val he
      · right;exact ⟨i,congrArg Subtype.val hi⟩
    exact C.val.spokes z.val hz'
  · intro z hz w hw
    have hz':z.val∈insert v.val (Set.range C.val.labels):=by
      rcases Set.mem_insert_iff.mp hz with he|⟨i,hi⟩
      · left;exact congrArg Subtype.val he
      · right;exact ⟨i,congrArg Subtype.val hi⟩
    have hw':w.val∈insert v.val (Set.range C.val.labels):=by
      rcases Set.mem_insert_iff.mp hw with he|⟨i,hi⟩
      · left;exact congrArg Subtype.val he
      · right;exact ⟨i,congrArg Subtype.val hi⟩
    exact C.val.independent z.val hz' w.val hw'

theorem ordinary_induced_transfer_injective (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (r:ℕ) (hr:3≤r) (v:A) (u u':B):
    Function.Injective (ordinaryInducedTransfer Q F H A B r hr v u u'):=by
  intro C D h
  apply Subtype.ext
  have hl: C.val.labels=D.val.labels:=by
    apply Function.Embedding.ext
    intro i
    have hh:=congrArg (fun E=>(E.labels i).val) h
    change C.val.labels i=D.val.labels i at hh
    exact hh
  have hinj:Function.Injective (fun E:OrdinaryTransferConfiguration hr Q F H v.val u.val u'.val=>E.labels):=by
    intro E G he
    cases E
    cases G
    cases he
    rfl
  exact hinj hl
end Oberwolfach
