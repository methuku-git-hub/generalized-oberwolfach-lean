module

public import Oberwolfach.MarkedWheelVertexEmbedding
public import Oberwolfach.MarkedProtectedResourceRestoration

@[expose] public section

/-! Exact inner restrictions of an embedded active packing. Excluding the
protected rows and hubs excludes their physical star, including successors
in marked rim edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U':Type} [DecidableEq V] [DecidableEq U]
  [DecidableEq V'] [DecidableEq U']

theorem markedResourceEmbedding_inner_iff (f:V↪V') (g:U↪U')
    (A:Finset V) (B:Finset U) (I:Finset V') (J:Finset U')
    (hA:∀ x,f x∈I↔x∈A) (hB:∀ u,g u∈J↔u∈B)
    (e:Finset V⊕(V×U)):
    markedInnerResource I J (markedResourceEmbedding f g e)↔markedInnerResource A B e:=by
  cases e with
  | inl e=>
    change e.image f⊆I↔e⊆A
    constructor
    · intro h x hx
      exact (hA x).mp (h (Finset.mem_image.mpr ⟨x,hx,rfl⟩))
    · intro h y hy
      obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
      exact (hA x).mpr (h hx)
  | inr z=>exact and_congr (hA z.1) (hB z.2)

theorem markedResourceEmbedding_inner_filter (f:V↪V') (g:U↪U')
    (A:Finset V) (B:Finset U) (I:Finset V') (J:Finset U')
    (hA:∀ x,f x∈I↔x∈A) (hB:∀ u,g u∈J↔u∈B)
    (S:Finset (Finset V⊕(V×U))):
    (S.image (markedResourceEmbedding f g)).filter (markedInnerResource I J)=
      (S.filter (markedInnerResource A B)).image (markedResourceEmbedding f g):=by
  rw [Finset.filter_image]
  congr 1
  ext e
  simp only [Finset.mem_filter,markedResourceEmbedding_inner_iff f g A B I J hA hB]

theorem markedResourceEmbedding_avoids_star (f:V↪V') (g:U↪U')
    (T:Finset V') (W:Finset U') (hf:∀ x,f x∉T) (hg:∀ u,g u∉W)
    (e:Finset V⊕(V×U)):
    ¬markedStarResource T W (markedResourceEmbedding f g e):=by
  cases e with
  | inl e=>
    rintro ⟨x,hx,hT⟩
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    exact hf y hT
  | inr z=>
    rintro (h|h)
    · exact hf z.1 h
    · exact hg z.2 h

theorem markedResourceEmbedding_active_inner_filter (f:V↪V') (g:U↪U')
    (I T:Finset V') (J W:Finset U') (hf:∀ x,f x∉T) (hg:∀ u,g u∉W)
    (S:Finset (Finset V⊕(V×U))):
    (S.image (markedResourceEmbedding f g)).filter (markedInnerResource I J)=
      (S.image (markedResourceEmbedding f g)).filter (markedInnerResource (I\T) (J\W)):=by
  ext e
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro he
  obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp he
  cases e with
  | inl e=>
    change e.image f⊆I↔e.image f⊆I\T
    constructor
    · intro h x hx
      obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
      exact Finset.mem_sdiff.mpr ⟨h (Finset.mem_image.mpr ⟨y,hy,rfl⟩),hf y⟩
    · intro h x hx
      exact (Finset.mem_sdiff.mp (h hx)).1
  | inr z=>
    change (f z.1∈I∧g z.2∈J)↔(f z.1∈I\T∧g z.2∈J\W)
    simp only [Finset.mem_sdiff,hf,hg,not_false_eq_true,and_true]

end Oberwolfach
