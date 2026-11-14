module

public import Oberwolfach.NeighbourPairAssignment

@[expose] public section

/-! Actual losses in the endpoint assignment and path choices after
rim and spoke deletions. The estimates are deterministic and use the
original domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem finite_domain_filter_deleted (A:Finset V) (P E:V→Prop) :
    (A.filter P).card≤(A.filter (fun v=>P v∧¬E v)).card+(Finset.univ.filter E).card := by
  have hs:A.filter P⊆A.filter (fun v=>P v∧¬E v)∪Finset.univ.filter E:=by
    intro v hv
    by_cases he:E v
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1,(Finset.mem_filter.mp hv).2,he⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

theorem bipartite_cut_deleted_column (H E:V→U→Prop) (L:ℝ)
    (hE:∀ u,((Finset.univ.filter (fun v=>E v u)).card:ℝ)≤L)
    (S:Finset V) (T:Finset U) :
    (bipartiteMatrixCut (fun v u=>if H v u then 1 else 0) S T:ℝ)≤
      (bipartiteMatrixCut (fun v u=>if H v u∧¬E v u then 1 else 0) S T:ℝ)+L*T.card := by
  have hpoint (u:U) : ((S.filter (fun v=>H v u)).card:ℝ)≤
      (S.filter (fun v=>H v u∧¬E v u)).card+L:=by
    have hh:=finite_domain_filter_deleted S (fun v=>H v u) (fun v=>E v u)
    have hh':((S.filter (fun v=>H v u)).card:ℝ)≤
        (S.filter (fun v=>H v u∧¬E v u)).card+(Finset.univ.filter (fun v=>E v u)).card:=by exact_mod_cast hh
    linarith only [hh',hE u]
  have hh:=Finset.sum_le_sum (s:=T) (fun u _=>hpoint u)
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero] at hh
  simp only [bipartiteMatrixCut,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [Finset.sum_comm (s:=S) (t:=T),Finset.sum_comm (s:=S) (t:=T)]
  simpa only [mul_comm] using hh

theorem two_rim_one_spoke_deleted (Q D:SimpleGraph V) (H E:V→U→Prop)
    (A:Finset V) (a b:V) (u:U) :
    ((A.filter (fun z=>H z u))∩Q.neighborFinset a∩Q.neighborFinset b).card≤
      ((A.filter (fun z=>H z u∧¬E z u))∩(Q\D).neighborFinset a∩(Q\D).neighborFinset b).card+
        D.degree a+D.degree b+(Finset.univ.filter (fun z=>E z u)).card := by
  let S:=(A.filter (fun z=>H z u))∩Q.neighborFinset a∩Q.neighborFinset b
  let T:=(A.filter (fun z=>H z u∧¬E z u))∩(Q\D).neighborFinset a∩(Q\D).neighborFinset b
  have hs:S⊆((T∪D.neighborFinset a)∪D.neighborFinset b)∪(Finset.univ.filter (fun z=>E z u)):=by
    intro z hz
    have hz':=hz
    simp only [S,Finset.mem_inter,Finset.mem_filter,SimpleGraph.mem_neighborFinset] at hz'
    by_cases hza:D.Adj a z
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ((D.mem_neighborFinset a z).mpr hza)))
    by_cases hzb:D.Adj b z
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((D.mem_neighborFinset b z).mpr hzb))
    by_cases he:E z u
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    simpa only [T,Finset.mem_inter,Finset.mem_filter,SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj] using
      And.intro (And.intro (And.intro hz'.1.1.1 (And.intro hz'.1.1.2 he)) (And.intro hz'.1.2 hza)) (And.intro hz'.2 hzb)
  have h₁:=(Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have h₂:=Finset.card_union_le (T∪D.neighborFinset a) (D.neighborFinset b)
  have h₃:=Finset.card_union_le T (D.neighborFinset a)
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at h₁ h₂ h₃
  change S.card≤T.card+D.degree a+D.degree b+(Finset.univ.filter (fun z=>E z u)).card
  omega

end Oberwolfach
