module

public import Oberwolfach.IndexedMarkedGraph

@[expose] public section

/-! Typed endpoint exchanges used in the actual expansion surgery.
Permuting heads of equal-type rim occurrences and hubs of equal-type
spoke occurrences preserves all four divisibility identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' A S:Type} [Fintype A] [Fintype S] [DecidableEq V] [DecidableEq U]

theorem finite_fiber_permutation (f:A→V) (τ:Equiv.Perm A) (v:V):
    Fintype.card {a:A // f (τ a)=v}=Fintype.card {a:A // f a=v}:=
  Fintype.card_congr (Equiv.subtypeEquiv τ (fun _=>Iff.rfl))

theorem finite_typed_fiber_permutation (f:A→V) (j:A→Bool) (τ:Equiv.Perm A)
    (hτ:∀ a,j (τ a)=j a) (v:V) (t:Bool):
    Fintype.card {a:A // f (τ a)=v∧j a=t}=Fintype.card {a:A // f a=v∧j a=t}:=by
  apply Fintype.card_congr (Equiv.subtypeEquiv τ _)
  intro a;simp only [hτ a]

def IndexedMarkedGraph.permuteHeads (G:IndexedMarkedGraph V U A S) (τ:Equiv.Perm A):IndexedMarkedGraph V U A S:=
  {G with dst:=G.dst∘τ}

def IndexedMarkedGraph.permuteHubs (G:IndexedMarkedGraph V U A S) (τ:Equiv.Perm S):IndexedMarkedGraph V U A S:=
  {G with hub:=G.hub∘τ}

theorem IndexedMarkedGraph.permuteHeads_balanced (G:IndexedMarkedGraph V U A S) (m:ℕ)
    (hG:G.IsBalanced m) (τ:Equiv.Perm A) (hτ:∀ a,G.jr (τ a)=G.jr a):
    (G.permuteHeads τ).IsBalanced m:=by
  constructor
  · intro v
    exact (finite_fiber_permutation G.dst τ v).trans (hG.directed v)
  · intro v
    exact (finite_fiber_permutation G.dst τ v).trans (hG.row v)
  · intro v
    exact (finite_typed_fiber_permutation G.dst G.jr τ hτ v true).trans (hG.marked v)
  · exact hG.hub

theorem IndexedMarkedGraph.permuteHubs_balanced (G:IndexedMarkedGraph V U A S) (m:ℕ)
    (hG:G.IsBalanced m) (τ:Equiv.Perm S) (hτ:∀ s,G.js (τ s)=G.js s):
    (G.permuteHubs τ).IsBalanced m:=by
  refine ⟨hG.directed,hG.row,hG.marked,?_⟩
  intro u
  change Fintype.card {s:S // G.hub (τ s)=u∧G.js s=false}=m*Fintype.card {s:S // G.hub (τ s)=u∧G.js s=true}
  rw [finite_typed_fiber_permutation G.hub G.js τ hτ u false,
    finite_typed_fiber_permutation G.hub G.js τ hτ u true]
  exact hG.hub u

theorem IndexedMarkedGraph.map_permuteHeads (G:IndexedMarkedGraph V U A S)
    (τ:Equiv.Perm A) (f:V→V') (g:U→U'):
    (G.permuteHeads τ).map f g=(G.map f g).permuteHeads τ:=rfl

theorem IndexedMarkedGraph.map_permuteHubs (G:IndexedMarkedGraph V U A S)
    (τ:Equiv.Perm S) (f:V→V') (g:U→U'):
    (G.permuteHubs τ).map f g=(G.map f g).permuteHubs τ:=rfl

end Oberwolfach
