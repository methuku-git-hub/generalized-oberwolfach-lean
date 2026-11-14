module

public import Oberwolfach.OrdinaryHistoryBoundaryDecompositionBalance
public import Oberwolfach.OrdinaryProtectedInnerPersistence

@[expose] public section
/-! A wheel deletion avoiding an inner physical pair has exactly balanced
boundary, so it contributes no error to the boundary-balance history. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_avoiding_wheel_boundary_balance
    (R:SimpleGraph V) (S:V→U→Prop) (I:Finset V) (J:Finset U) (r:ℕ)
    (hdec:HasOrdinaryWheelDecomposition R S r)
    (havoid:Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker I J)):
    ∀v,|((R\spanningRestriction R I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>S v u∧¬(v∈I∧u∈J))).card|≤0 :=by
  have hzero:=ordinary_protected_inner_zero R S I J havoid
  have hRzero:spanningRestriction R I=⊥:=by
    apply le_antisymm
    · intro x y hxy
      obtain ⟨hr,hx,hy⟩:=(spanningRestriction_adj R I x y).mp hxy
      have hh:(spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices I J)).Adj (Sum.inl x) (Sum.inl y):=
        (spanningRestriction_adj _ _ _ _).mpr ⟨hr,(ordinaryInnerVertices_left I J x).mpr hx,(ordinaryInnerVertices_left I J y).mpr hy⟩
      rw [hzero] at hh
      exact hh
    · exact bot_le
  have hSzero:∀v u,S v u→¬(v∈I∧u∈J):=by
    intro v u hs hmem
    have hh:(spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices I J)).Adj (Sum.inl v) (Sum.inr u):=
      (spanningRestriction_adj _ _ _ _).mpr ⟨hs,(ordinaryInnerVertices_left I J v).mpr hmem.1,(ordinaryInnerVertices_right I J u).mpr hmem.2⟩
    rw [hzero] at hh
    exact hh
  have hgraph:R\spanningRestriction R I=R:=by rw [hRzero];simp
  have hrow:∀v,(Finset.univ.filter (fun u=>S v u∧¬(v∈I∧u∈J)))=Finset.univ.filter (S v):=by
    intro v
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun h=>h.1,fun h=>⟨h,hSzero v u h⟩⟩
  obtain ⟨hbal,_⟩:=ordinary_wheel_decomposition_balance R S r hdec
  intro v
  have hd:((R\spanningRestriction R I).degree v:ℝ)=(R.degree v:ℝ):=by
    have hh:=congrArg (fun G:SimpleGraph V=>(G.degree v:ℝ)) hgraph
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  rw [hd,hrow v]
  have heq:(R.degree v:ℝ)=2*(Finset.univ.filter (S v)).card:=by exact_mod_cast hbal v
  rw [heq];norm_num
end Oberwolfach
