module

public import Oberwolfach.OrdinaryFourSequentialDecompositions
public import Oberwolfach.OrdinaryDeepBoundaryFourPieces
public import Oberwolfach.OrdinaryFourPieceDeepBlockerAvoidance
public import Oberwolfach.GraphFourPieceInnerDegreeSmall

@[expose] public section
/-! Four consecutive wheel families with the deep cover first: the later
approximate packing avoids the enclosing pair, cleanup has small degree,
and the final boundary finish avoids the deeper root star. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_four_piece_level_deep_blocker
    (Q A B C D F:SimpleGraph V) (H SA SB SC SD:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (ν η limit:ℝ)
    (hTX:T⊆X) (hWZ:W⊆Z)
    (hAhost:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources A SA))
    (hBhost:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources B SB))
    (hChost:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources C SC))
    (hDhost:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources D SD))
    (hAdec:HasOrdinaryWheelDecomposition A SA r) (hBdec:HasOrdinaryWheelDecomposition B SB r)
    (hCdec:HasOrdinaryWheelDecomposition C SC r) (hDdec:HasOrdinaryWheelDecomposition D SD r)
    (hBsub:B≤Q\A) (hSB:∀v u,SB v u→H v u∧¬SA v u)
    (hCsub:C≤(Q\A)\B) (hSC:∀v u,SC v u→(H v u∧¬SA v u)∧¬SB v u)
    (hDsub:D≤((Q\A)\B)\C) (hSD:∀v u,SD v u→((H v u∧¬SA v u)∧¬SB v u)∧¬SC v u)
    (hBinner:Disjoint (ordinaryPhysicalGraph B SB) (spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)))
    (hCdeg:∀w:V⊕U,((ordinaryPhysicalGraph C SC).degree w:ℝ)≤ν)
    (hAdeg:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph A SA) (ordinaryInnerVertices X Z)).degree w:ℝ)≤η)
    (hDdeg:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph D SD) (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit)
    (hAdeep:Disjoint (ordinaryPhysicalGraph A SA) (ordinaryDeepBlocker T W))
    (hCdeep:Disjoint (ordinaryPhysicalGraph C SC) (ordinaryDeepBlocker T W))
    (hDdeep:Disjoint (ordinaryPhysicalGraph D SD) (ordinaryDeepBlocker T W)):
    let R:=(((A⊔B)⊔C)⊔D);let S:=fun v u=>((SA v u∨SB v u)∨SC v u)∨SD v u;
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources R S) ∧
    HasOrdinaryWheelDecomposition R S r ∧
    Q\R=(((Q\A)\B)\C)\D ∧
    (fun v u=>H v u∧¬S v u)=(fun v u=>(((H v u∧¬SA v u)∧¬SB v u)∧¬SC v u)∧¬SD v u) ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤ν+η+limit) ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph R S T W) (ordinaryInnerVertices X Z)).degree w:ℝ)≤ν+η+limit) ∧
    Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker T W):=by
  intro R S
  have hBphys:ordinaryPhysicalGraph B SB≤ordinaryPhysicalGraph Q H:=by
    intro a b hab
    cases a with
    | inl v=>cases b with
      | inl w=>exact (hBsub hab).1
      | inr u=>exact (hSB v u hab).1
    | inr u=>cases b with
      | inl v=>exact (hSB v u hab).1
      | inr z=>exact hab.elim
  have hseq:=ordinary_four_sequential_decompositions Q A B C D F H SA SB SC SD r
    hAhost hBhost hChost hDhost hAdec hBdec hCdec hDdec hBsub hSB hCsub hSC hDsub hSD
  have hdeep:=ordinary_four_piece_deep_blocker_avoidance Q B C A D H SB SC SA SD X T Z W hTX hWZ hBphys hBinner hCdeep hAdeep hDdeep
  have hphys:ordinaryPhysicalGraph R S=((ordinaryPhysicalGraph B SB⊔ordinaryPhysicalGraph C SC)⊔
      ordinaryPhysicalGraph A SA)⊔ordinaryPhysicalGraph D SD:=by
    ext a b;cases a <;> cases b <;> simp [R,S,ordinaryPhysicalGraph] <;> tauto
  have hinner:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤ν+η+limit:=by
    intro w
    have hi:=graph_four_piece_inner_degree_small (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph B SB)
      (ordinaryPhysicalGraph C SC) (ordinaryPhysicalGraph A SA) (ordinaryPhysicalGraph D SD)
      (ordinaryInnerVertices X Z) ν η limit hBphys hBinner hCdeg hAdeg hDdeg w
    rw [←hphys] at hi
    convert hi using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  have hR : R = ((B⊔C)⊔A)⊔D := by
    ext v w; simp [R]; tauto
  have hS : S = (fun v u=>((SB v u∨SC v u)∨SA v u)∨SD v u) := by
    funext v u; apply propext; dsimp [S]; tauto
  have hboundary':∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph R S T W) (ordinaryInnerVertices X Z)).degree w:ℝ)≤ν+η+limit:=by
    intro w
    have hsub:spanningRestriction (ordinaryBoundaryGraph R S T W) (ordinaryInnerVertices X Z)≤
        spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z):=by
      intro a b hab
      have hh:=(spanningRestriction_adj _ _ _ _).mp hab
      have hb:=(ordinaryBoundaryGraph_adj _ _ _ _ _ _).mp hh.1
      exact (spanningRestriction_adj _ _ _ _).mpr ⟨hb.1,hh.2⟩
    have hh:((spanningRestriction (ordinaryBoundaryGraph R S T W) (ordinaryInnerVertices X Z)).degree w:ℝ)≤
        (spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:=by
      exact_mod_cast (SimpleGraph.degree_le_of_le hsub (v:=w))
    exact hh.trans (hinner w)
  have hdeep':Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker T W):=by
    rw [hR,hS]
    exact hdeep
  exact ⟨hseq.1,hseq.2.1,hseq.2.2.1,hseq.2.2.2,hinner,hboundary',hdeep'⟩
end Oberwolfach
