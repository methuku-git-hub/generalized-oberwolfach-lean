module

public import Oberwolfach.MarkedRootPair

@[expose] public section

/-! Finite directed rim and spoke occurrence data for the absorber's
abstract expansions. Loops and repeated formal pairs are permitted before
expansion; host physical injectivity is a separate, proved obligation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

structure IndexedMarkedGraph (V U A S:Type) where
  src:A→V
  dst:A→V
  row:S→V
  hub:S→U
  jr:A→Bool
  js:S→Bool

variable {V U V' U' A S:Type}

def IndexedMarkedGraph.map (G:IndexedMarkedGraph V U A S) (f:V→V') (g:U→U'):
    IndexedMarkedGraph V' U' A S:=
  ⟨f∘G.src,f∘G.dst,f∘G.row,g∘G.hub,G.jr,G.js⟩

structure IndexedMarkedGraph.IsBalanced [Fintype A] [Fintype S] [DecidableEq V] [DecidableEq U]
    (G:IndexedMarkedGraph V U A S) (m:ℕ):Prop where
  directed:∀ v,Fintype.card {a:A // G.dst a=v}=Fintype.card {a:A // G.src a=v}
  row:∀ v,Fintype.card {a:A // G.dst a=v}=Fintype.card {s:S // G.row s=v}
  marked:∀ v,Fintype.card {a:A // G.dst a=v∧G.jr a=true}=Fintype.card {s:S // G.row s=v∧G.js s=true}
  hub:∀ u,Fintype.card {s:S // G.hub s=u∧G.js s=false}=m*Fintype.card {s:S // G.hub s=u∧G.js s=true}

variable [Fintype V] [Fintype U] [Fintype V'] [Fintype U'] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']

theorem finite_fiber_composition (f:A→V) (g:V→V') (v:V'):
    Fintype.card {a:A // g (f a)=v}=
      ∑ w:{w:V // g w=v},Fintype.card {a:A // f a=w.val}:=by
  simpa only [and_true] using finite_typed_fiber_composition f g (fun _=>true) v true

theorem IndexedMarkedGraph.map_balanced (G:IndexedMarkedGraph V U A S) (m:ℕ)
    (hG:G.IsBalanced m) (f:V→V') (g:U→U'):(G.map f g).IsBalanced m:=by
  constructor
  · intro v
    change Fintype.card {a:A // f (G.dst a)=v}=Fintype.card {a:A // f (G.src a)=v}
    rw [finite_fiber_composition,finite_fiber_composition]
    exact Finset.sum_congr rfl (fun w _=>hG.directed w.val)
  · intro v
    change Fintype.card {a:A // f (G.dst a)=v}=Fintype.card {s:S // f (G.row s)=v}
    rw [finite_fiber_composition,finite_fiber_composition]
    exact Finset.sum_congr rfl (fun w _=>hG.row w.val)
  · intro v
    change Fintype.card {a:A // f (G.dst a)=v∧G.jr a=true}=Fintype.card {s:S // f (G.row s)=v∧G.js s=true}
    rw [finite_typed_fiber_composition,finite_typed_fiber_composition]
    exact Finset.sum_congr rfl (fun w _=>hG.marked w.val)
  · exact typed_fiber_balance_pushforward G.hub g G.js m hG.hub

variable {E K:Type} {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop}
    {π:Equiv.Perm V} {b m:ℕ}

def MarkedRootPair.indexed (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S):IndexedMarkedGraph V U A S:=
  ⟨G.src,G.dst,G.row,G.u,G.jr,G.js⟩

theorem MarkedRootPair.indexed_balanced (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S):
    G.indexed.IsBalanced m:=by
  refine ⟨fun v=>(G.rowBalance v).1,fun v=>(G.rowBalance v).2,?_,G.hubBalance⟩
  intro v
  have hh:=G.markedRowBalance v
  rw [finite_typed_fiber_filter_card G.dst G.jr v true,finite_typed_fiber_filter_card G.row G.js v true] at hh
  exact hh

end Oberwolfach
