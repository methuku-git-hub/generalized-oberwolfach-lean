module

public import Oberwolfach.ActualPrescribedBufferedMarkers
public import Oberwolfach.DisjointOrbitLabelsInjective

@[expose] public section
/-! A piece image can meet a prescribed marker label only at that same source
marker, provided every nonordinary piece vertex is matched to its source marker. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_anchor_cross_avoidance_from_marker_preimages
    {X V K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (ext:∀i:K,Fin (data.c*data.d+5)↪X)
    (hsupp:∀i∈data.s₁∪data.s₂,(data.P i).support=List.ofFn (ext i))
    (π:Equiv.Perm V) (root:K→V)
    (hinj:∀i,Function.Injective (fun j:Fin (data.d+1)=>(π^j.val) (root i)))
    (hdis:∀i j,i≠j→Disjoint (permutationWindow π 0 data.d (root i)) (permutationWindow π 0 data.d (root j)))
    (Ord:Finset V) (hOrd:∀i,Disjoint (permutationWindow π 0 data.d (root i)) Ord)
    (A:Finset X) (f:{x // x∈A}↪V) (g:{x // x∈data.prescribed}↪V)
    (hg:∀i (j:Fin (data.d+1)) (hj:bufferedMarker data.c data.d (ext i) j∈data.prescribed),
      g ⟨bufferedMarker data.c data.d (ext i) j,hj⟩=(π^j.val) (root i))
    (hpiece:∀y:{x // x∈A},f y∉Ord→
      ∃(i:K) (j:Fin (data.d+1)) (hm:bufferedMarker data.c data.d (ext i) j∈A),
        f y=(π^j.val) (root i) ∧
        f ⟨bufferedMarker data.c data.d (ext i) j,hm⟩=(π^j.val) (root i)):
    ∀x (hx:x∈data.prescribed) (hxa:x∉A) (y:{x // x∈A}),g ⟨x,hx⟩≠f y:=by
  classical
  intro x hx hxa y he
  obtain ⟨⟨i,j⟩,_,hmarker⟩:=Finset.mem_image.mp (actual_prescribed_subset_buffered_markers data ext hsupp hx)
  have hp:bufferedMarker data.c data.d (ext i) j∈data.prescribed:=by rw [hmarker];exact hx
  have hg':g ⟨x,hx⟩=(π^j.val) (root i):=by simpa only [hmarker] using hg i j hp
  have hwin:(π^j.val) (root i)∈permutationWindow π 0 data.d (root i):=by
    rw [permutationWindow_mem_iff]
    simp only [zero_add,pow_zero,Equiv.refl_apply]
    exact ⟨⟨j.val,by have hh:=j.isLt;omega⟩,rfl⟩
  have hnot:f y∉Ord:=by
    intro hh
    have hh':(π^j.val) (root i)∈Ord:=by rw [←hg',he];exact hh
    exact Finset.disjoint_left.mp (hOrd i) hwin hh'
  obtain ⟨i',j',hm,hy,hf⟩:=hpiece y hnot
  have hlab:(π^j.val) (root i)=(π^j'.val) (root i'):=hg'.symm.trans (he.trans hy)
  have hij:(i,j)=(i',j'):=disjoint_extended_orbit_labels_injective π data.d root hinj hdis hlab
  cases hij
  have hfy:f y=f ⟨bufferedMarker data.c data.d (ext i) j,hm⟩:=hy.trans hf.symm
  have hyx:y.val=bufferedMarker data.c data.d (ext i) j:=congrArg Subtype.val (f.injective hfy)
  apply hxa
  rw [←hmarker,←hyx]
  exact y.property
end Oberwolfach
