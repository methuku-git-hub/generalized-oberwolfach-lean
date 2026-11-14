module

public import Oberwolfach.PrescribedPositionEdgeChoice
public import Oberwolfach.PrescribedPositionClosedNeighbourhood

@[expose] public section
/-! Greedy induced-edge selection in a degree-two graph, with an arbitrary
initial set of excluded vertices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [Fintype X] [DecidableEq X]

def prescribedPairClosed (Q:SimpleGraph X) (e:X×X):Finset X:=
  prescribedClosedNeighbourhood Q e.1∪prescribedClosedNeighbourhood Q e.2

def prescribedPairsApart (Q:SimpleGraph X) (e f:X×X):Prop:=
  f.1∉prescribedPairClosed Q e ∧ f.2∉prescribedPairClosed Q e

theorem prescribed_position_greedy_pairs (Q:SimpleGraph X) (D:X→X→Prop)
    (hdeg:∀ x,Q.degree x≤2) (hrep:∀x y,Q.Adj x y→D x y ∨ D y x):
    ∀ m:ℕ,∀ S:Finset X,2*S.card+8*m≤Q.edgeFinset.card→
      ∃ es:List (X×X),es.length=m ∧
        (∀ e∈es,D e.1 e.2 ∧ Q.Adj e.1 e.2 ∧ e.1∉S ∧ e.2∉S) ∧
        es.Pairwise (prescribedPairsApart Q) := by
  intro m
  induction m with
  | zero =>
    intro S h
    exact ⟨[],rfl,by simp,by simp⟩
  | succ m ih =>
    intro S h
    have hlt:2*S.card<Q.edgeFinset.card:=by omega
    obtain ⟨u,v,huv,hu,hv⟩:=prescribed_position_edge_choice Q S hdeg hlt
    have hor:=hrep u v huv
    have hex:∃ e:X×X,D e.1 e.2 ∧ Q.Adj e.1 e.2 ∧ e.1∉S ∧ e.2∉S:=by
      rcases hor with hor|hor
      · exact ⟨(u,v),hor,huv,hu,hv⟩
      · exact ⟨(v,u),hor,huv.symm,hv,hu⟩
    obtain ⟨e,heD,heQ,he1,he2⟩:=hex
    let T:=S∪prescribedPairClosed Q e
    have hpairCard:(prescribedPairClosed Q e).card≤4:=prescribed_edge_closed_neighbourhood_card Q hdeg e.1 e.2 heQ
    have hT:T.card≤S.card+4:=(Finset.card_union_le _ _).trans (Nat.add_le_add_left hpairCard _)
    have hbudget:2*T.card+8*m≤Q.edgeFinset.card:=by omega
    obtain ⟨rest,hlen,hrest,hpair⟩:=ih T hbudget
    refine ⟨e::rest,by simp [hlen],?_,?_⟩
    · intro f hf
      rcases List.mem_cons.mp hf with hf|hf
      · subst f;exact ⟨heD,heQ,he1,he2⟩
      · obtain ⟨hfD,hfQ,hf1,hf2⟩:=hrest f hf
        refine ⟨hfD,hfQ,?_,?_⟩
        · intro hx;exact hf1 (Finset.mem_union_left _ hx)
        · intro hx;exact hf2 (Finset.mem_union_left _ hx)
    · apply List.pairwise_cons.mpr
      refine ⟨?_,hpair⟩
      intro f hf
      have hf1: f.1∉T:=(hrest f hf).2.2.1
      have hf2: f.2∉T:=(hrest f hf).2.2.2
      exact ⟨fun hx=>hf1 (Finset.mem_union_right _ hx),fun hx=>hf2 (Finset.mem_union_right _ hx)⟩
end Oberwolfach
