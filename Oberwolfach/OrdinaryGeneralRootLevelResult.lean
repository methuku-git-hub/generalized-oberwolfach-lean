module

public import Oberwolfach.OrdinaryGeneralFinishHostRootClearedResult

@[expose] public section
/-! An actual ordinary level decomposition, with a sharper boundary loss at
the nested deeper pair and preservation of its induced resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryGeneralRootLevelResult (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (m Kcap Dmax:ℕ) (ν η ρ:ℝ):Prop:=
    ∃R:SimpleGraph V,∃S:V→U→Prop,
      R≤Q ∧ (∀v u,S v u→H v u) ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=m+1)) (ordinaryHostResources R S) ∧
      HasOrdinaryWheelDecomposition R S (m+1) ∧
      let Qnext:=Q\R;let Hnext:=fun v u=>H v u∧¬S v u;
      Qnext≤spanningRestriction Q X ∧ (∀v u,Hnext v u→H v u∧v∈X∧u∈Z) ∧
      (∀v,Qnext.degree v=2*(Finset.univ.filter (Hnext v)).card) ∧
      (∀u,(m+1)∣(Finset.univ.filter (fun v=>Hnext v u)).card) ∧
      ordinaryHostResources Qnext Hnext⊆ordinaryRootResources X Z ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤
        ν+η+(2*(ρ*Fintype.card (V⊕U))+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ))) ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph R S T W) (ordinaryInnerVertices X Z)).degree w:ℝ)≤ν+η) ∧
      Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker T W)
end Oberwolfach
