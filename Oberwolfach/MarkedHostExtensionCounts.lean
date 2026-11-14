module

public import Oberwolfach.MarkedInitialDiagramConstruction

@[expose] public section

/-! The finite row and hub intersections used by the marked constructions.
These are actual cardinality inequalities, not graph-existence premises.
The two prescribed arc endpoints are distinct wherever a two-arc count
is used. At most two hub conditions, all of one type, are imposed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def markedArcPresent (tail head:E→V) (ktail khead:K→V) (j:Bool) (x y:V):Prop:=
  if j then ∃ e,ktail e=x∧khead e=y else ∃ e,tail e=x∧head e=y

def markedSpokesTo (H₀ HK:V→U→Prop) (j:Bool) (P:Finset U) (x:V):Prop:=
  ∀ u∈P,if j then HK x u else H₀ x u

structure MarkedHostExtensionCounts (tail head:E→V) (ktail khead:K→V)
    (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b l:ℕ) (c ch:ℝ):Prop where
  outgoing:∀ (j k:Bool) (x:V) (P:Finset U),P.card≤2→
    c≤((Finset.univ.filter (fun y=>markedArcPresent tail head ktail khead j x y∧markedSpokesTo H₀ HK k P y)).card:ℝ)
  incoming:∀ (j k:Bool) (x:V) (P:Finset U),P.card≤2→
    c≤((Finset.univ.filter (fun y=>markedArcPresent tail head ktail khead j y x∧markedSpokesTo H₀ HK k P y)).card:ℝ)
  twoOutgoing:∀ (k:Bool) (x y:V) (P:Finset U),x≠y→P.card≤2→
    c≤((Finset.univ.filter (fun z=>markedArcPresent tail head ktail khead false x z∧
      markedArcPresent tail head ktail khead false y z∧markedSpokesTo H₀ HK k P z)).card:ℝ)
  twoIncoming:∀ (j k:Bool) (x y:V) (P:Finset U),x≠y→P.card≤2→
    c≤((Finset.univ.filter (fun z=>markedArcPresent tail head ktail khead j z x∧
      markedArcPresent tail head ktail khead j z y∧markedSpokesTo H₀ HK k P z)).card:ℝ)
  twoStep:∀ (k:Bool) (x y:V) (P:Finset U),x≠y→P.card≤2→
    c≤((Finset.univ.filter (fun z=>markedArcPresent tail head ktail khead false x z∧
      markedArcPresent tail head ktail khead false z y∧markedSpokesTo H₀ HK k P z)).card:ℝ)
  hubs:∀ A Q:Finset V,Disjoint A Q→A.card+Q.card≤l+11→
    (∀ x∈A∪Q,∀ y∈A∪Q,x≠y→¬PermutationClose π b x y)→
    ch≤((Finset.univ.filter (fun u=>(∀ x∈A,H₀ x u)∧∀ x∈Q,HK x u)).card:ℝ)

@[simp] theorem markedSpokesTo_empty (H₀ HK:V→U→Prop) (j:Bool) (x:V):
    markedSpokesTo H₀ HK j ∅ x:=by simp [markedSpokesTo]

@[simp] theorem markedSpokesTo_singleton (H₀ HK:V→U→Prop) (j:Bool) (x:V) (u:U):
    markedSpokesTo H₀ HK j {u} x↔if j then HK x u else H₀ x u:=by simp [markedSpokesTo]

@[simp] theorem markedSpokesTo_pair (H₀ HK:V→U→Prop) (j:Bool) (x:V) (u u':U):
    markedSpokesTo H₀ HK j {u,u'} x↔
      (if j then HK x u else H₀ x u)∧(if j then HK x u' else H₀ x u'):=by simp [markedSpokesTo]

end Oberwolfach
