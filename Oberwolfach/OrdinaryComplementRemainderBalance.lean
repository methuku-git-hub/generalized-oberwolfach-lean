module

public import Oberwolfach.OrdinaryComplementPieceDegree
public import Oberwolfach.DisjointDegreeTwoRemainderBalance
public import Oberwolfach.OrdinaryComplementPieceDisjoint
public import Oberwolfach.OrdinaryReservedSpokeCardinality
public import Oberwolfach.FullFactorSetPackingToDecomposition

@[expose] public section
/-! The actual remainder obtained after embedding whole nonreserved
components has the exact ordinary rim/spoke balance and hub divisibility. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_complement_remainder_balance {n q r:ℕ}
    (G:SimpleGraph (Fin n)) (hG:G.IsRegularOfDegree (2*q))
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (C:∀u,Finset (F u).ConnectedComponent)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (fC:∀u,{x:Fin n // (F u).connectedComponentMk x∉C u}↪Fin n)
    (hC:∀u x y,((F u).induce {x | (F u).connectedComponentMk x∉C u}).Adj x y→G.Adj (fC u x) (fC u y))
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x:Fin n // (F u).connectedComponentMk x∉C u}
        ((F u).induce {x | (F u).connectedComponentMk x∉C u}) (fC u))
      (partialFactorPhysicalEdgesPoly {x:Fin n // (F v).connectedComponentMk x∉C v}
        ((F v).induce {x | (F v).connectedComponentMk x∉C v}) (fC v))):
    (∀x,(G \ ordinaryEmbeddedComplements F C fC).degree x=
      2*(Finset.univ.filter (fun u=>x∉Set.range (fC u))).card) ∧
    (∀u,r∣(Finset.univ.filter (fun x=>x∉Set.range (fC u))).card) :=by
  let T:Fin q→SimpleGraph (Fin n):=fun u=>((F u).induce {x | (F u).connectedComponentMk x∉C u}).map (fC u)
  have hsub:∀u,T u≤G:=by
    intro u x y hxy
    obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj (fC u) _ _ _).1 hxy
    exact hC u a b hab
  have hdis:∀u v,u≠v→Disjoint (T u).edgeFinset (T v).edgeFinset:=
    ordinary_complement_piece_disjoint F C fC hCC
  have hUnion:ordinaryEmbeddedComplements F C fC=⨆u,T u:=rfl
  have hUnionSub:ordinaryEmbeddedComplements F C fC≤G:=by rw [hUnion];exact iSup_le hsub
  constructor
  · have hdeg:∀u x,(T u).degree x=if x∈Set.range (fC u) then 2 else 0:=
      fun u x=>ordinary_complement_piece_degree (F u) (hF u) (C u) (fC u) x
    have hbalance:=disjoint_degree_two_remainder_balance G hG T (fun u x=>x∈Set.range (fC u)) hsub (by
      intro u v huv
      have hh:=hdis u v huv
      convert hh using 1 <;> apply graph_edge_finset_instance_eq) (by
      intro u x
      have hh:=hdeg u x
      simp only [←SimpleGraph.ncard_neighborSet] at hh ⊢
      by_cases hx:x∈Set.range (fC u) <;> simp only [hx,ite_true,ite_false] at hh ⊢ <;> exact hh)
    intro x
    have hh:=hbalance x
    simp only [←SimpleGraph.ncard_neighborSet] at hh ⊢
    rw [hUnion]
    convert hh using 1
    congr 1
    apply congrArg Finset.card
    ext u
    simp

  · intro u
    have hh:=ordinary_reserved_spoke_cardinality (F u) (C u) (hsize u) (fC u)
      (fun x=>x∉Set.range (fC u)) (fun _=>Iff.rfl)
    have hcount:(Finset.univ.filter (fun x=>x∉Set.range (fC u))).card=r*(C u).card:=by
      convert hh.1 using 1
      apply congrArg Finset.card
      ext x
      simp
    rw [hcount]
    exact dvd_mul_right r (C u).card
end Oberwolfach
