module

public import Oberwolfach.OrdinaryRootFirstLevelFromStarFinish
public import Oberwolfach.OrdinaryNestedRootInnerFourPieces

@[expose] public section
/-! Retain the smaller edit bound on an intermediate pair when the actual
finish avoids its star. The root cover and cleanup are still charged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_level_larger_star
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T Tplus:Finset V) (Z W Wplus:Finset U)
    (r:ℕ) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W r η ell t ν D σ) (limit:ℝ)
    (E:OrdinaryRootFirstFinishData Q F H X T Z W r η ell t ν D σ O limit)
    (hplusX:Tplus⊆X) (hplusZ:Wplus⊆Z)
    (hstar:Disjoint (ordinaryPhysicalGraph E.rim E.spokes) (ordinaryDeepRootStar Tplus Wplus))
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
    (∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph R S T W) (ordinaryInnerVertices X Z)).degree w:ℝ)≤ν+η) ∧
    Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker T W) ∧
    (∀Y⊆Tplus,∀J⊆Wplus,∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices Y J)).degree w:ℝ)≤ν+η):=by
  intro K B SB C SC R S
  have hl:=ordinary_root_first_level_from_star_finish Q F H X T Z W r η ell t ν D σ O limit E hbal hdiv
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
  have hR:R=((B⊔C)⊔K.cover.rim)⊔E.rim:=by
    ext v w;simp [R];tauto
  have hS:S=(fun v u=>((SB v u∨SC v u)∨K.cover.spokes v u)∨E.spokes v u):=by
    funext v u;apply propext;dsimp [S];tauto
  refine ⟨hl.1,hl.2.1,hl.2.2.1,hl.2.2.2.1,hl.2.2.2.2.1,hl.2.2.2.2.2.1,hl.2.2.2.2.2.2,?_⟩
  intro Y hY J hJ w
  rw [hR,hS]
  exact ordinary_nested_root_inner_four_pieces Q B C K.cover.rim E.rim H SB SC K.cover.spokes E.spokes
    X Y Tplus Z J Wplus ν η (hY.trans hplusX) (hJ.trans hplusZ) hY hJ
    hBphys hb.2.2.2.2 O.cleanup.degree K.cover.inner_degree hstar w
end Oberwolfach
