module

public import Oberwolfach.OrdinaryGeneralHostCoverDownResult
public import Oberwolfach.OrdinaryHostResourcesRemainder

@[expose] public section
/-! Convert a conflict-respecting general wheel cover-down into the exact
resource step used by the balanced level-chain theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_general_resource_level_step
    (P Q F:SimpleGraph V) (Hbase H:V→U→Prop) (X:Finset V) (Z:Finset U) (r:ℕ) (t:ℝ)
    (hQP:Q≤P) (hH:∀v u,H v u→Hbase v u)
    (hstep:OrdinaryGeneralHostCoverDownResult Q F H X Z r t):
    ∃T:Finset (Sym2 V⊕(V×U)),
      T⊆ordinaryHostResources Q H ∧ T⊆ordinaryRootResources X Z ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r))
        (ordinaryHostResources Q H\T) ∧
      ∃(Qnext:SimpleGraph V) (Hnext:V→U→Prop),ordinaryHostResources Qnext Hnext=T ∧
        (∀v,Qnext.degree v=2*(Finset.univ.filter (Hnext v)).card) ∧
        (∀u,r∣(Finset.univ.filter (fun v=>Hnext v u)).card) ∧
        ∃(A:SimpleGraph V) (S:V→U→Prop),A≤Q ∧ (∀v u,S v u→H v u) ∧
          Qnext=Q\A ∧ Hnext=(fun v u=>H v u∧¬S v u) ∧
          (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph A S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤t):=by
  obtain ⟨A,S,hA,hS,hdec,hroot,hbal,hdiv,hdegree⟩:=hstep
  let Qnext:=Q\A
  let Hnext:=fun v u=>H v u∧¬S v u
  let T:=ordinaryHostResources Qnext Hnext
  have hrem:=ordinary_host_resources_remainder Q A H S hA hS
  have hdec':=resource_decomposition_map ordinaryWheelResources ordinaryWheelResources
    (ordinaryWheelToLarger (F:=F) (r:=r) hQP hH) (ordinaryWheelToLarger_resources hQP hH)
    (ordinaryHostResources A S) hdec
  refine ⟨T,?_,hroot,?_,Qnext,Hnext,rfl,?_,?_,A,S,hA,hS,rfl,rfl,hdegree⟩
  · rw [show T=ordinaryHostResources Q H\ordinaryHostResources A S from hrem.1]
    exact Finset.sdiff_subset
  · rw [show ordinaryHostResources Q H\T=ordinaryHostResources A S from hrem.2]
    exact hdec'
  · convert hbal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hdiv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
