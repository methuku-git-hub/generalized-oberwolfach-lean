module

public import Oberwolfach.PrescribedPositionSelectionNodup
public import Oberwolfach.PrescribedEmbeddingZipUpdate

@[expose] public section
/-! Zipping matching-edge endpoint lists maps both endpoints of each source
arc to the corresponding endpoints of the target arc. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V:Type} [DecidableEq X] [DecidableEq V]

theorem prescribed_position_pair_vertex_zip:
    ∀ (es:List (X×X)) (ms:List (V×V)),es.length=ms.length→∀ (vs:List X) (zs:List V),
      (es.flatMap prescribedPairVertices++vs).zip (ms.flatMap prescribedPairVertices++zs)=
        (es.zip ms).flatMap (fun p=>[(p.1.1,p.2.1),(p.1.2,p.2.2)])++vs.zip zs := by
  intro es
  induction es with
  | nil =>
    intro ms h vs zs
    cases ms with
    | nil => simp [prescribedPairVertices]
    | cons m ms => simp at h
  | cons e es ih =>
    intro ms h vs zs
    cases ms with
    | nil => simp at h
    | cons m ms =>
      have hl:es.length=ms.length:=by simpa using h
      simp only [List.flatMap_cons,prescribedPairVertices,List.cons_append,List.nil_append,
        List.zip_cons_cons]
      rw [ih ms hl vs zs]

theorem prescribed_position_pair_zip_members (es:List (X×X)) (ms:List (V×V))
    (hlen:es.length=ms.length) (vs:List X) (zs:List V) (e:X×X) (m:V×V) (h:(e,m)∈es.zip ms):
    (e.1,m.1)∈(es.flatMap prescribedPairVertices++vs).zip (ms.flatMap prescribedPairVertices++zs) ∧
    (e.2,m.2)∈(es.flatMap prescribedPairVertices++vs).zip (ms.flatMap prescribedPairVertices++zs) := by
  rw [prescribed_position_pair_vertex_zip es ms hlen vs zs]
  constructor <;> apply List.mem_append_left
  · apply List.mem_flatMap.mpr
    exact ⟨(e,m),h,by simp⟩
  · apply List.mem_flatMap.mpr
    exact ⟨(e,m),h,by simp⟩
end Oberwolfach
