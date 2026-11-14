module

public import Oberwolfach.MarkedFiniteResourceOperations
public import Oberwolfach.MarkedWheelVertexEmbedding

@[expose] public section

/-! Finite typed resources commute with invariant row and hub embeddings.
The equality records each marked physical successor, not just the number
of occurrences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K E' K':Type}
  [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [Fintype V'] [Fintype U'] [Fintype E'] [Fintype K']
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
  [DecidableEq V'] [DecidableEq U'] [DecidableEq E'] [DecidableEq K']

theorem markedFiniteResources_embedding
    (tail head:E→V) (ktail khead:K→V) (tail' head':E'→V') (ktail' khead':K'→V')
    (f:V↪V') (g:U↪U') (ρ:Equiv.Perm V) (π:Equiv.Perm V') (hf:∀ x,f (ρ x)=π (f x))
    (e:E↪E') (k:K↪K') (het:∀ a,tail' (e a)=f (tail a)) (heh:∀ a,head' (e a)=f (head a))
    (hkt:∀ a,ktail' (k a)=f (ktail a)) (hkh:∀ a,khead' (k a)=f (khead a))
    (A:Finset (E⊕K)) (S:Finset (V×U)):
    (markedFiniteResources tail head ktail khead ρ A S).image (markedResourceEmbedding f g)=
      markedFiniteResources tail' head' ktail' khead' π (A.image (e.sumMap k)) (S.image (Prod.map f g)):=by
  have hp (a:E⊕K):(markedPhysicalEdge tail head ktail khead ρ a).image f=
      markedPhysicalEdge tail' head' ktail' khead' π ((e.sumMap k) a):=by
    cases a <;> simp only [markedPhysicalEdge,Sum.elim_inl,Sum.elim_inr,
      Function.Embedding.sumMap,Function.Embedding.coeFn_mk,Sum.map_inl,Sum.map_inr,
      Finset.image_insert,Finset.image_singleton,het,heh,hkt,hkh,hf]
  unfold markedFiniteResources
  rw [Finset.image_union,Finset.image_image,Finset.image_image,Finset.image_image,Finset.image_image]
  congr 1
  · apply Finset.image_congr
    intro a _
    change Sum.inl ((markedPhysicalEdge tail head ktail khead ρ a).image f)=
      (Sum.inl (markedPhysicalEdge tail' head' ktail' khead' π ((e.sumMap k) a)):Finset V'⊕(V'×U'))
    rw [hp]

end Oberwolfach
