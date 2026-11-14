module

public import Oberwolfach.OrdinaryRootCoverNonrootData
public import Oberwolfach.MarkedActiveDeletionDegrees

@[expose] public section
/-! The strong nonroot degree bound of the actual root cover is a uniform
physical degree bound after pulling it back to the nonroot domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_nonroot_comap_degree (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ)
    (D:OrdinaryRootCoverNonrootData Q F H X T Z W r η ell):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    ∀a:A⊕B,(((ordinaryPhysicalGraph D.rim D.spokes).comap (φ.sumMap ψ)).degree a:ℝ)≤ell:=by
  intro A B φ ψ a
  have ha:(φ.sumMap ψ) a∉ordinaryInnerVertices T W:=by
    cases a with
    | inl v=>
      apply mt (ordinaryInnerVertices_left T W v.val).mp
      exact (Finset.mem_sdiff.mp v.property).2
    | inr u=>
      apply mt (ordinaryInnerVertices_right T W u.val).mp
      exact (Finset.mem_sdiff.mp u.property).2
  have hh:=graph_comap_injective_degree_le (ordinaryPhysicalGraph D.rim D.spokes) (φ.sumMap ψ) a
  have hb:=D.nonroot_degree ((φ.sumMap ψ) a) ha
  have hc:((((ordinaryPhysicalGraph D.rim D.spokes).comap (φ.sumMap ψ)).degree a):ℝ)≤
      ((ordinaryPhysicalGraph D.rim D.spokes).degree ((φ.sumMap ψ) a):ℝ):=by exact_mod_cast hh
  exact hc.trans hb
end Oberwolfach
