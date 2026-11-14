module

public import Oberwolfach.OrdinaryDeepBoundaryFourPiecesRootFreeCleanup
public import Oberwolfach.OrdinaryRootFirstLevelFromDeepFinish
public import Oberwolfach.OrdinaryRootFirstFinishDataDeep
public import Oberwolfach.OrdinaryDeepBoundaryFourPieces

@[expose] public section
/-! The actual root-star-free finish contributes nothing to the deep
boundary; only the root cover and cleanup contribute to that degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_level_from_root_free_cleanup
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W r η ell t ν D σ) (limit:ℝ)
    (E:OrdinaryRootFirstFinishData Q F H X T Z W r η ell t ν D σ O limit)
    (hcleanup:Disjoint (ordinaryPhysicalGraph (wheelFamilyRim O.cleanup.wheels)
      (wheelFamilySpokes O.cleanup.wheels)) (ordinaryDeepRootStar T W))
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card):
    let K:=O.context;
    let B:=ordinaryRootFirstPackingRim Q F H X T Z W r η ell t K;
    let SB:=ordinaryRootFirstPackingSpokes Q F H X T Z W r η ell t K;
    let C:=wheelFamilyRim O.cleanup.wheels;let SC:=wheelFamilySpokes O.cleanup.wheels;
    let R:=(((K.cover.rim⊔B)⊔C)⊔E.rim);
    let S:=fun v u=>((K.cover.spokes v u∨SB v u)∨SC v u)∨E.spokes v u;
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources R S) ∧
    HasOrdinaryWheelDecomposition R S r ∧
    (Q\R).support⊆(X:Set V) ∧ (∀v u,H v u∧¬S v u→v∈X∧u∈Z) ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤ν+η+limit) ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph R S T W) (ordinaryInnerVertices X Z)).degree w:ℝ)≤η) ∧
    Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker T W):=by
  intro K B SB C SC R S
  have hl:=ordinary_root_first_level_from_deep_finish Q F H X T Z W r η ell t ν D σ O limit
    (ordinary_root_first_finish_data_deep Q F H X T Z W r η ell t ν D σ O limit E) hbal hdiv
  have hb:=ordinary_root_first_packing_ambient_facts Q F H X T Z W r η ell t K
  have hBphys:ordinaryPhysicalGraph B SB≤ordinaryPhysicalGraph Q H:=by
    intro a b hab
    cases a with
    | inl v=>cases b with
      | inl w=>exact (hb.2.2.1 hab).1
      | inr u=>exact (hb.2.2.2.1 v u hab).1
    | inr u=>cases b with
      | inl v=>exact (hb.2.2.2.1 v u hab).1
      | inr z=>exact hab.elim
  have hboundary:=ordinary_deep_boundary_four_pieces_root_free_cleanup Q B C K.cover.rim E.rim H SB SC K.cover.spokes E.spokes
    X T Z W η hBphys hb.2.2.2.2 hcleanup K.cover.inner_degree E.avoids_star
  have hR:R=((B⊔C)⊔K.cover.rim)⊔E.rim:=by
    ext v w;simp [R];tauto
  have hS:S=(fun v u=>((SB v u∨SC v u)∨K.cover.spokes v u)∨E.spokes v u):=by
    funext v u;apply propext;dsimp [S];tauto
  have hbnd:∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph R S T W) (ordinaryInnerVertices X Z)).degree w:ℝ)≤η:=by
    rw [hR,hS]
    exact hboundary
  exact ⟨hl.1,hl.2.1,hl.2.2.1,hl.2.2.2.1,hl.2.2.2.2.1,hbnd,hl.2.2.2.2.2.2⟩
end Oberwolfach
