module

public import Oberwolfach.DisjointGraphFamilyExactDegree

@[expose] public section
/-! Removing disjoint degree-two pieces from a 2q-regular graph leaves
exactly two rim edges for every missing piece at each vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem disjoint_degree_two_remainder_balance {V:Type} [Fintype V] [DecidableEq V] {q:ℕ}
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree (2*q))
    (T:Fin q→SimpleGraph V) (occ:Fin q→V→Prop)
    (hsub:∀u,T u≤G)
    (hdis:∀u v,u≠v→Disjoint (T u).edgeFinset (T v).edgeFinset)
    (hdeg:∀u x,(T u).degree x=if occ u x then 2 else 0):
    ∀x,(G \ (⨆u,T u)).degree x=2*(Finset.univ.filter (fun u=>¬occ u x)).card :=by
  intro x
  rw [graph_degree_sdiff G _ (iSup_le hsub) x,hG x,disjoint_graph_family_exact_degree T hdis]
  simp_rw [hdeg]
  have hsum:(∑u:Fin q,if occ u x then 2 else 0)=2*(Finset.univ.filter (fun u=>occ u x)).card:=by
    simp [Finset.sum_ite,Nat.mul_comm]
  rw [hsum]
  have hp:=Finset.card_filter_add_card_filter_not (s:=(Finset.univ:Finset (Fin q))) (fun u=>occ u x)
  simp only [Finset.card_univ,Fintype.card_fin] at hp
  omega
end Oberwolfach
