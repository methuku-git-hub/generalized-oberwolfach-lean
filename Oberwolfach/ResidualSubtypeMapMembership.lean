module

public import Oberwolfach.ResidualSubtypePieces

@[expose] public section
/-! The restriction map neither loses nor identifies edges and directed arcs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem source_subtype_edges_membership (R:Finset V)
    (qs:List (PrescribedSourcePiece {x // x∈R}))
    (ps:List (PrescribedSourcePiece V))
    (hmap:qs.map (fun q=>q.map Subtype.val)=ps)
    (e:Sym2 {x // x∈R}):
    e∈sourcePieceEdgesUnion qs ↔ Sym2.map Subtype.val e∈sourcePieceEdgesUnion ps := by
  rw [←hmap,source_piece_map_edges_union]
  constructor
  · intro he;exact Finset.mem_image.mpr ⟨e,he,rfl⟩
  · intro he
    obtain ⟨d,hd,heq⟩:=Finset.mem_image.mp he
    have :d=e:=(Sym2.map.injective Subtype.val_injective) heq
    simpa [this] using hd

theorem source_subtype_arcs_membership (R:Finset V)
    (qs:List (PrescribedSourcePiece {x // x∈R}))
    (ps:List (PrescribedSourcePiece V))
    (hmap:qs.map (fun q=>q.map Subtype.val)=ps)
    (x y:{x // x∈R}):
    (x,y)∈sourcePieceArcsUnion qs ↔ (x.1,y.1)∈sourcePieceArcsUnion ps := by
  rw [←hmap,source_piece_map_arcs_union]
  constructor
  · intro he;exact Finset.mem_image.mpr ⟨(x,y),he,rfl⟩
  · intro he
    obtain ⟨⟨a,b⟩,hab,heq⟩:=Finset.mem_image.mp he
    have ha:a=x:=Subtype.ext (congrArg Prod.fst heq)
    have hb:b=y:=Subtype.ext (congrArg Prod.snd heq)
    simpa [ha,hb] using hab
end Oberwolfach
