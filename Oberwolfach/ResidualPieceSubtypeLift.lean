module

public import Oberwolfach.ResidualFamilyFixedOrientation

@[expose] public section
/-! Lift a source piece whose vertices lie in a set to the corresponding
vertex subtype, without requiring that the set be nonempty. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem source_piece_lift_to_vertex_subtype (R:Finset V) (p:PrescribedSourcePiece V)
    (hR:p.vertices.toFinset⊆R):
    ∃ q:PrescribedSourcePiece {x // x∈R},q.map Subtype.val=p := by
  cases p with
  | path xs =>
    have hx:∀x∈xs,x∈R := by
      intro x hx
      exact hR (List.mem_toFinset.mpr hx)
    let ys:List {x // x∈R}:=xs.pmap (fun x hx=>⟨x,hx⟩) hx
    have hmap:ys.map Subtype.val=xs := by
      simp [ys,List.map_pmap,List.pmap_eq_map_attach]
    refine ⟨.path ys,?_⟩
    simpa [PrescribedSourcePiece.map] using hmap
  | cycle a xs =>
    have ha:a∈R := hR (by simp [PrescribedSourcePiece.vertices])
    have hx:∀x∈xs,x∈R := by
      intro x hx
      apply hR
      simp [PrescribedSourcePiece.vertices,hx]
    let ys:List {x // x∈R}:=xs.pmap (fun x hx=>⟨x,hx⟩) hx
    have hmap:ys.map Subtype.val=xs := by
      simp [ys,List.map_pmap,List.pmap_eq_map_attach]
    refine ⟨.cycle ⟨a,ha⟩ ys,?_⟩
    simpa [PrescribedSourcePiece.map] using hmap
end Oberwolfach
