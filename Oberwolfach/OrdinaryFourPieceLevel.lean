module

public import Oberwolfach.OrdinaryFourSequentialDecompositions
public import Oberwolfach.OrdinaryDeepBoundaryFourPieces
public import Oberwolfach.OrdinaryDeepBlockerLeStar
public import Oberwolfach.GraphFourPieceInnerDegreeSmall
public import Oberwolfach.OrdinaryFourPieceDeepAvoidance

@[expose] public section
/-! Combine four actual wheel families and retain both the usual inner
cost and the sharper boundary cost at a deeper nested pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_four_piece_level
    (Q A B C D F:SimpleGraph V) (H SA SB SC SD:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (ν η limit:ℝ)
    (hTX:T⊆X) (hWZ:W⊆Z)
    (hAhost:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources A SA))
    (hBhost:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources B SB))
    (hChost:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources C SC))
    (hDhost:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources D SD))
    (hAdec:HasOrdinaryWheelDecomposition A SA r) (hBdec:HasOrdinaryWheelDecomposition B SB r)
    (hCdec:HasOrdinaryWheelDecomposition C SC r) (hDdec:HasOrdinaryWheelDecomposition D SD r)
    (hAsub:ordinaryPhysicalGraph A SA≤ordinaryPhysicalGraph Q H)
    (hBsub:B≤Q\A) (hSB:∀v u,SB v u→H v u∧¬SA v u)
    (hCsub:C≤(Q\A)\B) (hSC:∀v u,SC v u→(H v u∧¬SA v u)∧¬SB v u)
    (hDsub:D≤((Q\A)\B)\C) (hSD:∀v u,SD v u→((H v u∧¬SA v u)∧¬SB v u)∧¬SC v u)
    (hAinner:Disjoint (ordinaryPhysicalGraph A SA) (spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)))
    (hBdeg:∀w:V⊕U,((ordinaryPhysicalGraph B SB).degree w:ℝ)≤ν)
    (hCdeg:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph C SC) (ordinaryInnerVertices X Z)).degree w:ℝ)≤η)
    (hDdeg:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph D SD) (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit)
    (hBdeep:Disjoint (ordinaryPhysicalGraph B SB) (ordinaryDeepBlocker T W))
    (hCdeep:Disjoint (ordinaryPhysicalGraph C SC) (ordinaryDeepBlocker T W))
    (hDstar:Disjoint (ordinaryPhysicalGraph D SD) (ordinaryDeepRootStar T W)):
    let R:=(((A⊔B)⊔C)⊔D);let S:=fun v u=>((SA v u∨SB v u)∨SC v u)∨SD v u;
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources R S) ∧
    HasOrdinaryWheelDecomposition R S r ∧
    Q\R=(((Q\A)\B)\C)\D ∧
    (fun v u=>H v u∧¬S v u)=(fun v u=>(((H v u∧¬SA v u)∧¬SB v u)∧¬SC v u)∧¬SD v u) ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤ν+η+limit) ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph R S T W) (ordinaryInnerVertices X Z)).degree w:ℝ)≤ν+η) ∧
    Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker T W):=by
  intro R S
  have hseq:=ordinary_four_sequential_decompositions Q A B C D F H SA SB SC SD r
    hAhost hBhost hChost hDhost hAdec hBdec hCdec hDdec hBsub hSB hCsub hSC hDsub hSD
  have hboundary:=ordinary_deep_boundary_four_pieces Q A B C D H SA SB SC SD X T Z W ν η hAsub hAinner hBdeg hCdeg hDstar
  have hphys:ordinaryPhysicalGraph R S=((ordinaryPhysicalGraph A SA⊔ordinaryPhysicalGraph B SB)⊔
      ordinaryPhysicalGraph C SC)⊔ordinaryPhysicalGraph D SD:=by
    ext a b;cases a <;> cases b <;> simp [R,S,ordinaryPhysicalGraph]
  have hdeep:Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker T W):=
    ordinary_four_piece_deep_avoidance Q A B C D H SA SB SC SD X T Z W hTX hWZ hAsub hAinner hBdeep hCdeep hDstar
  have hinner:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤ν+η+limit:=by
    intro w
    have hi:=graph_four_piece_inner_degree_small (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph A SA)
      (ordinaryPhysicalGraph B SB) (ordinaryPhysicalGraph C SC) (ordinaryPhysicalGraph D SD)
      (ordinaryInnerVertices X Z) ν η limit hAsub hAinner hBdeg hCdeg hDdeg w
    rw [←hphys] at hi
    convert hi using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  exact ⟨hseq.1,hseq.2.1,hseq.2.2.1,hseq.2.2.2,hinner,hboundary,hdeep⟩
end Oberwolfach
