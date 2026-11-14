module

public import Oberwolfach.OrdinaryLocalPostRootControls
public import Oberwolfach.OrdinaryInnerFactorSurvival

@[expose] public section
/-! Exact boundary, local class-change and inner factor-survival inputs after
three sequential physical deletions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_local_root_cover_selection_data
    (Q₀ Q₂ Qfactor Rroot:SimpleGraph V) (H₀ H₂ Hfactor Sroot:V→U→Prop)
    (X:Finset V) (Z:Finset U) (C D:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool)
    (L ν η ell:ℝ)
    (hbase:ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q₀ H₀) (ordinaryInnerVertices X Z))
    (hC:Disjoint C (spanningRestriction (ordinaryPhysicalGraph Q₀ H₀) (ordinaryInnerVertices X Z)))
    (hpost:ordinaryPhysicalGraph Q₂ H₂=(ordinaryPhysicalGraph Q₀ H₀\C)\D)
    (hL:∀w,((((ordinaryBoundaryGraph Q₀ H₀ X Z)\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree w:ℝ)+
      (D.degree w:ℝ)≤L)
    (hD:∀w,(D.degree w:ℝ)≤ν)
    (hEinner:∀w,((spanningRestriction (ordinaryPhysicalGraph Rroot Sroot) (ordinaryInnerVertices X Z)).degree w:ℝ)≤η)
    (hEouter:∀w∉ordinaryInnerVertices X Z,((ordinaryPhysicalGraph Rroot Sroot).degree w:ℝ)≤ell):
    let Q₃:=Q₂\Rroot;let H₃:=fun v u=>H₂ v u∧¬Sroot v u;
    let E:=ordinaryPhysicalGraph Rroot Sroot;
    let K:=D⊔spanningRestriction E (ordinaryInnerVertices X Z);
    ordinaryBoundaryGraph Q₃ H₃ X Z=((ordinaryBoundaryGraph Q₀ H₀ X Z\C)\(D⊔E)) ∧
    ordinaryBoundaryGraph Q₃ H₃ X Z≤((ordinaryBoundaryGraph Q₀ H₀ X Z\C)\D) ∧
    (∀w∉ordinaryInnerVertices X Z,((((ordinaryBoundaryGraph Q₀ H₀ X Z)\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree w:ℝ)+
      ((D⊔E).degree w:ℝ)≤L+ell) ∧
    (∀w,(K.degree w:ℝ)≤ν+η) ∧
    ordinaryPhysicalGraph Qfactor Hfactor\K≤ordinaryPhysicalGraph Q₃ H₃:=by
  intro Q₃ H₃ E K
  have hG:ordinaryPhysicalGraph Q₃ H₃=((ordinaryPhysicalGraph Q₀ H₀\C)\D)\E:=by
    rw [ordinary_physical_graph_typed_deletion,hpost]
  have hsup:((ordinaryPhysicalGraph Q₀ H₀\C)\D)\E=
      (ordinaryPhysicalGraph Q₀ H₀\C)\(D⊔E):=by
    ext a b;simp only [SimpleGraph.sdiff_adj,SimpleGraph.sup_adj];tauto
  have hphys:ordinaryPhysicalGraph Q₃ H₃=(ordinaryPhysicalGraph Q₀ H₀\C)\(D⊔E):=hG.trans hsup
  have hb:=ordinary_boundary_after_physical_packings Q₀ Q₃ H₀ H₃ X Z C (D⊔E) hphys
  have hsupport:ordinaryBoundaryGraph Q₃ H₃ X Z≤((ordinaryBoundaryGraph Q₀ H₀ X Z\C)\D):=by
    rw [hb]
    intro a b hab
    exact ⟨hab.1,fun hd=>hab.2 (Or.inl hd)⟩
  have hclass:=ordinary_local_root_cover_class_bounds (ordinaryBoundaryGraph Q₀ H₀ X Z) C D E
    (retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ) (ordinaryInnerVertices X Z) L ell hL hEouter
  have hK:∀w,(K.degree w:ℝ)≤ν+η:=by
    intro w
    have hd:=graph_degree_sup_le D (spanningRestriction E (ordinaryInnerVertices X Z)) w
    have hdR:(K.degree w:ℝ)≤(D.degree w:ℝ)+((spanningRestriction E (ordinaryInnerVertices X Z)).degree w:ℝ):=by
      exact_mod_cast hd
    linarith only [hdR,hD w,hEinner w]
  have hkeep:=ordinary_factor_survives_local_root_cover (ordinaryPhysicalGraph Q₀ H₀)
    (ordinaryPhysicalGraph Qfactor Hfactor) C D E (ordinaryPhysicalGraph Q₃ H₃) X Z hbase hC hG
  exact ⟨hb,hsupport,hclass,hK,hkeep⟩
end Oberwolfach
