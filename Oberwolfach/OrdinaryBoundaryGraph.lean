module

public import Oberwolfach.BipartiteRelationGraph
public import Oberwolfach.OrdinaryDecompositionEdges
public import Oberwolfach.EdgeRetention
public import Oberwolfach.FiniteProductProjection

@[expose] public section

/-! The three ordinary boundary reservoirs as one physical simple graph.
Rim vertices and hubs occupy distinct summands. Rim edges and spokes have
injective physical coordinates, so independent edge retention samples every
physical boundary edge exactly once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryPhysicalGraph (Q:SimpleGraph V) (H:V→U→Prop):SimpleGraph (V⊕U) where
  Adj x y:=match x,y with
    | Sum.inl v,Sum.inl w=>Q.Adj v w
    | Sum.inl v,Sum.inr u=>H v u
    | Sum.inr u,Sum.inl v=>H v u
    | Sum.inr _,Sum.inr _=>False
  symm:=⟨by intro x y;cases x <;> cases y <;> simp only;exact fun h=>h.symm;all_goals tauto⟩
  loopless:=⟨by intro x;cases x <;> simp only;exact Q.irrefl;exact not_false⟩

def ordinaryPhysicalResource:Sym2 V⊕(V×U)→Sym2 (V⊕U)
  | Sum.inl e=>e.map Sum.inl
  | Sum.inr (v,u)=>s(Sum.inl v,Sum.inr u)

theorem ordinaryPhysicalResource_injective:
    Function.Injective (ordinaryPhysicalResource (V:=V) (U:=U)):=by
  intro e f he
  cases e with
  | inl e=>
    induction e using Sym2.ind with
    | _ x y=>
      cases f with
      | inl f=>
        induction f using Sym2.ind with
        | _ z w=>
          change s(Sum.inl x,Sum.inl y)=s(Sum.inl z,Sum.inl w) at he
          rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩|⟨h1,h2⟩
          · simp only [Sum.inl.injEq] at h1 h2;subst z;subst w;rfl
          · simp only [Sum.inl.injEq] at h1 h2
            subst w;subst z;exact congrArg Sum.inl (Sym2.eq_swap)
      | inr f=>
        rcases f with ⟨v,u⟩
        change s(Sum.inl x,Sum.inl y)=s(Sum.inl v,Sum.inr u) at he
        rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩|⟨h1,h2⟩
        · exact (Sum.inl_ne_inr h2).elim
        · exact (Sum.inl_ne_inr h1).elim
  | inr e=>
    rcases e with ⟨v,u⟩
    cases f with
    | inl f=>
      induction f using Sym2.ind with
      | _ x y=>
        change s(Sum.inl v,Sum.inr u)=s(Sum.inl x,Sum.inl y) at he
        rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩|⟨h1,h2⟩
        · exact (Sum.inr_ne_inl h2).elim
        · exact (Sum.inr_ne_inl h2).elim
    | inr f=>
      rcases f with ⟨w,a⟩
      change s(Sum.inl v,Sum.inr u)=s(Sum.inl w,Sum.inr a) at he
      rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩|⟨h1,h2⟩
      · simp only [Sum.inl.injEq,Sum.inr.injEq] at h1 h2;subst w;subst a;rfl
      · exact (Sum.inl_ne_inr h1).elim

def ordinaryInnerVertices (I:Finset V) (J:Finset U):Finset (V⊕U):=
  I.image Sum.inl∪J.image Sum.inr

theorem ordinaryInnerVertices_left (I:Finset V) (J:Finset U) (v:V):
    Sum.inl v∈ordinaryInnerVertices I J↔v∈I:=by
  simp [ordinaryInnerVertices]

theorem ordinaryInnerVertices_right (I:Finset V) (J:Finset U) (u:U):
    Sum.inr u∈ordinaryInnerVertices I J↔u∈J:=by
  simp [ordinaryInnerVertices]

def ordinaryBoundaryGraph (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U):SimpleGraph (V⊕U):=
  bipartiteRelationGraph (Finset.univ\ordinaryInnerVertices I J) (ordinaryInnerVertices I J)
    Finset.sdiff_disjoint (ordinaryPhysicalGraph Q H).Adj

theorem ordinaryBoundaryGraph_adj (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U)
    (x y:V⊕U):
    (ordinaryBoundaryGraph Q H I J).Adj x y↔
      (ordinaryPhysicalGraph Q H).Adj x y ∧
        ((x∉ordinaryInnerVertices I J ∧ y∈ordinaryInnerVertices I J) ∨
         (y∉ordinaryInnerVertices I J ∧ x∈ordinaryInnerVertices I J)):=by
  simp only [ordinaryBoundaryGraph,bipartiteRelationGraph,Finset.mem_sdiff,Finset.mem_univ,true_and]
  have hs: (ordinaryPhysicalGraph Q H).Adj y x↔(ordinaryPhysicalGraph Q H).Adj x y:=SimpleGraph.adj_comm _ y x
  rw [hs];tauto

theorem retained_boundary_rim (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U)
    (σ:Sym2 (V⊕U)→Bool) (x y:V) (hx:x∉I) (hy:y∈I):
    (retainedGraph (ordinaryBoundaryGraph Q H I J) σ).Adj (Sum.inl x) (Sum.inl y)↔
      Q.Adj x y ∧ σ (ordinaryPhysicalResource (Sum.inl s(x,y)))=true:=by
  simp only [retainedGraph,ordinaryBoundaryGraph_adj,ordinaryInnerVertices_left,hx,hy,
    not_false_eq_true,not_true_eq_false,true_and,false_and,or_false,and_true]
  rfl

theorem retained_boundary_row (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U)
    (σ:Sym2 (V⊕U)→Bool) (x:V) (u:U) (hx:x∉I) (hu:u∈J):
    (retainedGraph (ordinaryBoundaryGraph Q H I J) σ).Adj (Sum.inl x) (Sum.inr u)↔
      H x u ∧ σ (ordinaryPhysicalResource (Sum.inr (x,u)))=true:=by
  simp only [retainedGraph,ordinaryBoundaryGraph_adj,ordinaryInnerVertices_left,ordinaryInnerVertices_right,hx,hu,
    not_false_eq_true,not_true_eq_false,true_and,false_and,or_false,and_true]
  rfl

theorem retained_boundary_column (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U)
    (σ:Sym2 (V⊕U)→Bool) (x:V) (u:U) (hx:x∈I) (hu:u∉J):
    (retainedGraph (ordinaryBoundaryGraph Q H I J) σ).Adj (Sum.inl x) (Sum.inr u)↔
      H x u ∧ σ (ordinaryPhysicalResource (Sum.inr (x,u)))=true:=by
  simp only [retainedGraph,ordinaryBoundaryGraph_adj,ordinaryInnerVertices_left,ordinaryInnerVertices_right,hx,hu,
    not_false_eq_true,not_true_eq_false,true_and,false_and,false_or,and_true]
  rfl


theorem ordinary_physical_retention_law (τ:ℝ) (hτ:0≤τ) (hτ1:τ≤1):
    (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin τ hτ hτ1)).map
      (fun σ e=>σ (ordinaryPhysicalResource e))=
      FiniteLaw.pi (fun _:Sym2 V⊕(V×U)=>FiniteLaw.retentionCoin τ hτ hτ1):=by
  exact finiteLaw_pi_injective_projection _ ordinaryPhysicalResource ordinaryPhysicalResource_injective

end Oberwolfach
