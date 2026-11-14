module

public import Oberwolfach.PrescribedPositionZipPairs
public import Oberwolfach.PrescribedEmbeddingZipImage

@[expose] public section
/-! Pair selected source arcs and singleton positions with target arcs and
singleton images, extending the prescribed partial injection. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V:Type} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]

def prescribedInducedArcs (D:X→X→Prop) (A:Finset X):Finset (X×X):=
  Finset.univ.filter (fun e=>e.1∈A ∧ e.2∈A ∧ D e.1 e.2)

theorem prescribed_pair_vertices_length (es:List (X×X)):
    (es.flatMap prescribedPairVertices).length=2*es.length := by
  induction es with
  | nil => simp
  | cons e es ih => simp [prescribedPairVertices,ih];omega

theorem prescribed_position_pairing (D:X→X→Prop) (A:Finset X) (f:X→V)
    (hinj:Set.InjOn f (↑A:Set X))
    (es:List (X×X)) (ms:List (V×V)) (vs:List X) (zs:List V)
    (hlen:es.length=ms.length) (hvlen:vs.length=zs.length)
    (hsource:(es.flatMap prescribedPairVertices++vs).Nodup)
    (htarget:(ms.flatMap prescribedPairVertices++zs).Nodup)
    (hdisS:∀x∈es.flatMap prescribedPairVertices++vs,x∉A)
    (hdisT:∀y∈ms.flatMap prescribedPairVertices++zs,y∉A.image f)
    (hsel:∀e∈es,D e.1 e.2)
    (honly:∀ x y,D x y→x∈A∪(es.flatMap prescribedPairVertices++vs).toFinset→
      y∈A∪(es.flatMap prescribedPairVertices++vs).toFinset→(x,y)∈es):
    let B:=A∪(es.flatMap prescribedPairVertices++vs).toFinset;
    ∃ g:X→V,Set.InjOn g (↑B:Set X) ∧ (∀x∈A,g x=f x) ∧
      B.image g=A.image f∪(ms.flatMap prescribedPairVertices++zs).toFinset ∧
      (prescribedInducedArcs D B).image (Prod.map g g)=ms.toFinset := by
  intro B
  let as:=es.flatMap prescribedPairVertices++vs
  let bs:=ms.flatMap prescribedPairVertices++zs
  have hlen':as.length=bs.length:=by
    dsimp [as,bs]
    simp only [List.length_append,prescribed_pair_vertices_length]
    omega
  let g:=updatePairedImages f (as.zip bs)
  have hupdate:=prescribed_embedding_zip_update as bs hlen' hsource htarget A f hinj hdisS hdisT
  have himage:=prescribed_embedding_zip_image as bs hlen' hsource htarget A f hinj hdisS hdisT
  have hfst:(es.zip ms).map Prod.fst=es:=List.map_fst_zip hlen.le
  have hsnd:(es.zip ms).map Prod.snd=ms:=List.map_snd_zip hlen.ge
  have hpair:∀ (e:X×X) (m:V×V),(e,m)∈es.zip ms → g e.1=m.1 ∧ g e.2=m.2:=by
    intro e m he
    have hp:=prescribed_position_pair_zip_members es ms hlen vs zs e m he
    exact ⟨hupdate.2.2 _ hp.1,hupdate.2.2 _ hp.2⟩
  refine ⟨g,hupdate.1,hupdate.2.1,himage,?_⟩
  ext a
  constructor
  · intro ha
    obtain ⟨e,he,heq⟩:=Finset.mem_image.mp ha
    have he':e.1∈B ∧ e.2∈B ∧ D e.1 e.2:=by
      have hh:=Finset.mem_filter.mp he
      exact hh.2
    have heSel:(e.1,e.2)∈es:=honly e.1 e.2 he'.2.2 he'.1 he'.2.1
    have hzip:e∈(es.zip ms).map Prod.fst:=by rw [hfst];simpa using heSel
    obtain ⟨p,hp,hpe⟩:=List.mem_map.mp hzip
    have hpmap:=hpair p.1 p.2 (by simpa using hp)
    have hm:p.2∈ms:=by rw [←hsnd];exact List.mem_map.mpr ⟨p,hp,rfl⟩
    apply List.mem_toFinset.mpr
    have hpEq:Prod.map g g e=p.2:=by
      rw [←hpe]
      exact Prod.ext hpmap.1 hpmap.2
    rw [←heq,hpEq]
    exact hm
  · intro ha
    have hm: a∈ms:=List.mem_toFinset.mp ha
    have hm':a∈(es.zip ms).map Prod.snd:=by rw [hsnd];exact hm
    obtain ⟨p,hp,hpa⟩:=List.mem_map.mp hm'
    have hpmap:=hpair p.1 p.2 (by simpa using hp)
    have he:p.1∈es:=by rw [←hfst];exact List.mem_map.mpr ⟨p,hp,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨p.1,?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_,?_,hsel p.1 he⟩
      · apply Finset.mem_union_right
        apply List.mem_toFinset.mpr
        apply List.mem_append_left
        apply List.mem_flatMap.mpr
        exact ⟨p.1,he,by simp [prescribedPairVertices]⟩
      · apply Finset.mem_union_right
        apply List.mem_toFinset.mpr
        apply List.mem_append_left
        apply List.mem_flatMap.mpr
        exact ⟨p.1,he,by simp [prescribedPairVertices]⟩
    · exact (Prod.ext hpmap.1 hpmap.2).trans hpa
end Oberwolfach
