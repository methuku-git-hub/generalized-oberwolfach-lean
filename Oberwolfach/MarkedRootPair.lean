module

public import Oberwolfach.MarkedRootGraphSupport
public import Oberwolfach.MarkedPaddingActualHubBalance

@[expose] public section

/-! A pair of actual finite typed root graphs and an edge-bijective map.
Vertex maps may identify vertices. Injectivity is required only for the
physical rim and spoke occurrence maps. The balance fields are the exact
marked wheel divisibility identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U]

structure MarkedRootPair (tail head:E→V) (ktail khead:K→V)
    (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b m:ℕ) (A S:Type) [Fintype A] [Fintype S] where
  src:A→V
  dst:A→V
  row:S→V
  φ:V→V
  ψ:U→U
  u:S→U
  u':S→U
  jr:A→Bool
  js:S→Bool
  R:Finset V
  R':Finset V
  B:Finset U
  disjointRows:Disjoint R R'
  rimRoots:∀ e,src e∈R∧dst e∈R∧φ (src e)∈R'∧φ (dst e)∈R'
  spokeRoots:∀ s,row s∈R∧φ (row s)∈R'
  hubRoots:∀ s,u s∈B∧u' s∈B
  hubMap:∀ s,u' s=ψ (u s)
  differentHubs:∀ s,u s≠u' s
  sourceArcSeparation:∀ e,¬PermutationClose π b (src e) (dst e)
  imageArcSeparation:∀ e,¬PermutationClose π b (φ (src e)) (φ (dst e))
  fourRootSeparation:∀ e,∀ x∈({src e,dst e,φ (src e),φ (dst e)}:Finset V),
    ∀ y∈({src e,dst e,φ (src e),φ (dst e)}:Finset V),x≠y→¬PermutationClose π b x y
  rowBalance:∀ v,Fintype.card {e:A // dst e=v}=Fintype.card {e:A // src e=v}∧
    Fintype.card {e:A // dst e=v}=Fintype.card {s:S // row s=v}
  markedRowBalance:∀ v,(Finset.univ.filter (fun e:{e:A // dst e=v}=>jr e.val=true)).card=
    (Finset.univ.filter (fun s:{s:S // row s=v}=>js s.val=true)).card
  hubBalance:∀ z,Fintype.card {s:S // u s=z∧js s=false}=m*Fintype.card {s:S // u s=z∧js s=true}
  sourceRimInjective:Function.Injective (fun e=>if jr e then ({src e,π (dst e)}:Finset V) else {src e,dst e})
  imageRimInjective:Function.Injective (fun e=>if jr e then ({φ (src e),π (φ (dst e))}:Finset V) else {φ (src e),φ (dst e)})
  sourceSpokeInjective:Function.Injective (fun s=>(row s,u s))
  imageSpokeInjective:Function.Injective (fun s=>(φ (row s),u' s))
  rimPresent:∀ e,if jr e then (∃ k,ktail k=src e∧khead k=dst e)∧(∃ k,ktail k=φ (src e)∧khead k=φ (dst e))
    else (∃ k,tail k=src e∧head k=dst e)∧(∃ k,tail k=φ (src e)∧head k=φ (dst e))
  spokePresent:∀ s,if js s then HK (row s) (u s)∧HK (φ (row s)) (u' s) else H₀ (row s) (u s)∧H₀ (φ (row s)) (u' s)

variable {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}

def MarkedRootPair.source (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S):Finset (Finset V⊕(V×U)):=
  markedRootGraphResources π G.src G.dst G.row G.jr G.u

def MarkedRootPair.image (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S):Finset (Finset V⊕(V×U)):=
  markedRootGraphResources π (fun e=>G.φ (G.src e)) (fun e=>G.φ (G.dst e)) (fun s=>G.φ (G.row s)) G.jr G.u'

theorem finite_typed_fiber_filter_card {X Y:Type} [Fintype X] [DecidableEq Y] (f:X→Y) (j:X→Bool) (y:Y) (t:Bool):
    (Finset.univ.filter (fun x:{x:X // f x=y}=>j x.val=t)).card=Fintype.card {x:X // f x=y∧j x=t}:=by
  rw [←Fintype.card_subtype]
  exact Fintype.card_congr {
    toFun:=fun x=>⟨x.val.val,x.val.property,x.property⟩
    invFun:=fun x=>⟨⟨x.val,x.property.1⟩,x.property.2⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl}

theorem MarkedRootPair.filtered_hub_balance (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S):
    ∀ z,(Finset.univ.filter (fun s:{s:S // G.u s=z}=>G.js s.val=false)).card=
      m*(Finset.univ.filter (fun s:{s:S // G.u s=z}=>G.js s.val=true)).card:=by
  intro z
  rw [finite_typed_fiber_filter_card G.u G.js z false,finite_typed_fiber_filter_card G.u G.js z true]
  exact G.hubBalance z

theorem MarkedRootPair.old_resources (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S):
    ∀ e∈G.source∪G.image,MarkedOldResource tail head ktail khead π (G.R∪G.R') G.B e:=by
  have h₁:∀ a,if G.jr a then ∃ k,ktail k=G.src a∧khead k=G.dst a else ∃ e,tail e=G.src a∧head e=G.dst a:=by
    intro a;have hh:=G.rimPresent a;cases hj:G.jr a <;> simp only [hj,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
    all_goals exact hh.1
  have h₂:∀ a,if G.jr a then ∃ k,ktail k=G.φ (G.src a)∧khead k=G.φ (G.dst a)
      else ∃ e,tail e=G.φ (G.src a)∧head e=G.φ (G.dst a):=by
    intro a;have hh:=G.rimPresent a;cases hj:G.jr a <;> simp only [hj,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
    all_goals exact hh.2
  have hl:=marked_root_graph_old_supported (π:=π) G.src G.dst G.row G.jr G.u (G.R∪G.R') G.B
    (fun a=>⟨Finset.mem_union_left _ (G.rimRoots a).1,Finset.mem_union_left _ (G.rimRoots a).2.1⟩)
    (fun a=>⟨Finset.mem_union_left _ (G.spokeRoots a).1,(G.hubRoots a).1⟩) h₁
  have hr:=marked_root_graph_old_supported (π:=π) (fun a=>G.φ (G.src a)) (fun a=>G.φ (G.dst a))
    (fun s=>G.φ (G.row s)) G.jr G.u' (G.R∪G.R') G.B
    (fun a=>⟨Finset.mem_union_right _ (G.rimRoots a).2.2.1,Finset.mem_union_right _ (G.rimRoots a).2.2.2⟩)
    (fun a=>⟨Finset.mem_union_right _ (G.spokeRoots a).2,(G.hubRoots a).2⟩) h₂
  intro e he;rcases Finset.mem_union.mp he with he|he
  · exact (hl e he).1
  · exact (hr e he).1

end Oberwolfach
