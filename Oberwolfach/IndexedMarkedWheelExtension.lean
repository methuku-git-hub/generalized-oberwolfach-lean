module

public import Oberwolfach.IndexedMarkedGraph
public import Oberwolfach.MarkedPaddingHubDegrees

@[expose] public section

/-! Adjoin one disjoint abstract wheel per chosen occurrence. This is the
base graph for the marked expansion; later typed exchanges replace the
old rim arcs and spokes with their crossed versions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A S I:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S] [Fintype I]
    [DecidableEq V] [DecidableEq U] [DecidableEq I]

def indexedMarkedWheelExtension (G:IndexedMarkedGraph V U A S) (m:ℕ):
    IndexedMarkedGraph (V⊕(I×Fin (m+1))) (U⊕I) (A⊕(I×Fin (m+1))) (S⊕(I×Fin (m+1))):=
  {src:=paddingRimTail (Sum.inl∘G.src) (fun i k=>Sum.inr (i,k))
   dst:=paddingRimHead (Sum.inl∘G.dst) (fun i k=>Sum.inr (i,k))
   row:=paddingSpokeRow (Sum.inl∘G.row) (fun i k=>Sum.inr (i,k))
   hub:=paddingSpokeHub G.hub m
   jr:=paddingRimType G.jr m
   js:=paddingSpokeType G.js m}

theorem indexedMarkedWheelExtension_balanced (G:IndexedMarkedGraph V U A S) (m:ℕ)
    (hG:G.IsBalanced m):(indexedMarkedWheelExtension (I:=I) G m).IsBalanced m:=by
  let f:V→V⊕(I×Fin (m+1)):=Sum.inl
  have hmap:=G.map_balanced m hG f id
  have hmrow:∀ v:V⊕(I×Fin (m+1)),(Finset.univ.filter (fun a:{a:A // f (G.dst a)=v}=>G.jr a.val=true)).card=
      (Finset.univ.filter (fun s:{s:S // f (G.row s)=v}=>G.js s.val=true)).card:=by
    intro v
    calc
      _ = Fintype.card {a:A // f (G.dst a)=v∧G.jr a=true} := by
        exact finite_typed_fiber_filter_card (fun a=>f (G.dst a)) G.jr v true
      _ = Fintype.card {s:S // f (G.row s)=v∧G.js s=true} := hmap.marked v
      _ = _ := (finite_typed_fiber_filter_card (fun s=>f (G.row s)) G.js v true).symm
  have hbase:=padding_row_balance (f∘G.src) (f∘G.dst) (f∘G.row) G.jr G.js m
    (fun i k=>Sum.inr (i,k):I→Fin (m+1)→V⊕(I×Fin (m+1)))
    (fun v=>⟨hmap.directed v,hmap.row v⟩) hmrow
  refine ⟨fun v=>(hbase.1 v).1,fun v=>(hbase.1 v).2,?_,?_⟩
  · intro v
    have hh:=hbase.2 v
    rw [finite_typed_fiber_filter_card,finite_typed_fiber_filter_card] at hh
    exact hh
  · exact padding_hub_balance G.hub G.js m hG.hub

theorem indexedMarkedWheelExtension_old_src (G:IndexedMarkedGraph V U A S) (m:ℕ) (a:A):
    (indexedMarkedWheelExtension (I:=I) G m).src (Sum.inl a)=Sum.inl (G.src a):=rfl

theorem indexedMarkedWheelExtension_old_dst (G:IndexedMarkedGraph V U A S) (m:ℕ) (a:A):
    (indexedMarkedWheelExtension (I:=I) G m).dst (Sum.inl a)=Sum.inl (G.dst a):=rfl

theorem indexedMarkedWheelExtension_private_src (G:IndexedMarkedGraph V U A S) (m:ℕ) (i:I) (k:Fin (m+1)):
    (indexedMarkedWheelExtension (I:=I) G m).src (Sum.inr (i,k))=Sum.inr (i,k):=rfl

theorem indexedMarkedWheelExtension_private_dst (G:IndexedMarkedGraph V U A S) (m:ℕ) (i:I) (k:Fin (m+1)):
    (indexedMarkedWheelExtension (I:=I) G m).dst (Sum.inr (i,k))=Sum.inr (i,finRotate (m+1) k):=rfl

end Oberwolfach
