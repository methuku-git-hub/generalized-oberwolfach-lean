module

public import Oberwolfach.OrdinaryTriangleCoverDownFromSample
public import Oberwolfach.GraphSingleEdge

@[expose] public section
/-! Inner degree of three successive wheel families: the first avoids the
inner host, the second has bounded degree, and the third has bounded inner degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_inner_union_degree
    (Q A B C:SimpleGraph V) (H S T W:V→U→Prop) (X:Finset V) (Z:Finset U) (b c:ℝ)
    (hA:A≤Q) (hS:∀v u,S v u→H v u)
    (havoid:Disjoint (ordinaryPhysicalGraph A S)
      (spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)))
    (hB:∀w,((ordinaryPhysicalGraph B T).degree w:ℝ)≤b)
    (hC:∀w,((spanningRestriction (ordinaryPhysicalGraph C W) (ordinaryInnerVertices X Z)).degree w:ℝ)≤c):
    ∀w,((spanningRestriction (ordinaryPhysicalGraph ((A⊔B)⊔C) (fun v u=>(S v u∨T v u)∨W v u))
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤b+c:=by
  let I:=ordinaryInnerVertices X Z
  let GA:=ordinaryPhysicalGraph A S
  let GB:=ordinaryPhysicalGraph B T
  let GC:=ordinaryPhysicalGraph C W
  let G0:=ordinaryPhysicalGraph Q H
  have hAphys:GA≤G0:=by
    intro a b hab
    cases a with
    | inl v=>cases b with
      | inl w=>exact hA hab
      | inr u=>exact hS v u hab
    | inr u=>cases b with
      | inl v=>exact hS v u hab
      | inr u'=>exact hab.elim
  have hphys:ordinaryPhysicalGraph ((A⊔B)⊔C) (fun v u=>(S v u∨T v u)∨W v u)=(GA⊔GB)⊔GC:=by
    ext a b
    cases a with
    | inl v=>cases b with
      | inl w=>rfl
      | inr u=>rfl
    | inr u=>cases b with
      | inl v=>rfl
      | inr u'=>simp [ordinaryPhysicalGraph,GA,GB,GC]
  have hsub:spanningRestriction ((GA⊔GB)⊔GC) I≤GB⊔spanningRestriction GC I:=by
    intro a b hab
    have hh:=(spanningRestriction_adj _ I a b).mp hab
    have hnot:¬GA.Adj a b:=by
      intro ha
      have hi:(spanningRestriction G0 I).Adj a b:=(spanningRestriction_adj G0 I a b).mpr ⟨hAphys ha,hh.2⟩
      exact (disjoint_iff_inf_le.mp havoid) ⟨ha,hi⟩
    rcases hh.1 with (ha|hb)|hc
    · exact (hnot ha).elim
    · exact Or.inl hb
    · exact Or.inr ((spanningRestriction_adj GC I a b).mpr ⟨hc,hh.2⟩)
  intro w
  have hd:=SimpleGraph.degree_le_of_le hsub (v:=w)
  have hsum:=graph_degree_sup_le GB (spanningRestriction GC I) w
  have hd':((spanningRestriction ((GA⊔GB)⊔GC) I).degree w:ℝ)≤((GB⊔spanningRestriction GC I).degree w:ℝ):=by
    have hh:=(Nat.cast_le (α:=ℝ)).mpr hd
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hs':((GB⊔spanningRestriction GC I).degree w:ℝ)≤(GB.degree w:ℝ)+(spanningRestriction GC I).degree w:=by
    have hh:=(Nat.cast_le (α:=ℝ)).mpr hsum
    push_cast at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hb:(GB.degree w:ℝ)≤b:=by convert hB w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hc:((spanningRestriction GC I).degree w:ℝ)≤c:=by convert hC w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hout:((spanningRestriction ((GA⊔GB)⊔GC) I).degree w:ℝ)≤b+c:=by linarith only [hd',hs',hb,hc]
  convert hout using 1 <;> congr! 8 <;> first | exact hphys | exact Subsingleton.elim _ _
end Oberwolfach
