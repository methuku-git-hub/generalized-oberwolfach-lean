module

public import Oberwolfach.MarkedPermutationEmbedding
public import Oberwolfach.MarkedWheelRestriction
public import Oberwolfach.ResourceDecompositions

@[expose] public section

/-! Embed actual marked wheels from invariant active row and hub domains.
The two arc maps preserve direction and type; the resource map is injective,
so physical disjointness is preserved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K E' K':Type} [DecidableEq V] [DecidableEq U]
  [DecidableEq V'] [DecidableEq U']
  {tail head:E→V} {ktail khead:K→V} {tail' head':E'→V'} {ktail' khead':K'→V'}
  {m b:ℕ} {ρ:Equiv.Perm V} {π:Equiv.Perm V'} {H₀ HK:V→U→Prop} {H₀' HK':V'→U'→Prop}

def markedResourceEmbedding (f:V↪V') (g:U↪U'):(Finset V⊕(V×U))↪(Finset V'⊕(V'×U')):=
  (⟨Finset.image f,Finset.image_injective f.injective⟩:Finset V↪Finset V').sumMap (f.prodMap g)

def markedWheelVertexEmbedding
    (f:V↪V') (g:U↪U') (hcomm:∀ x,f (ρ x)=π (f x))
    (e:E→E') (k:K→K')
    (het:∀ a,tail' (e a)=f (tail a)) (heh:∀ a,head' (e a)=f (head a))
    (hkt:∀ a,ktail' (k a)=f (ktail a)) (hkh:∀ a,khead' (k a)=f (khead a))
    (hH₀:∀ x u,H₀ x u→H₀' (f x) (g u)) (hHK:∀ x u,HK x u→HK' (f x) (g u)):
    MarkedWheel tail head ktail khead m ρ b H₀ HK↪
      MarkedWheel tail' head' ktail' khead' m π b H₀' HK' where
  toFun W:=⟨⟨f∘W.1.val,
    (permutationSeparated_embedding_iff f ρ π hcomm b W.1.val).mpr W.1.property.1,
    fun i=>by
      obtain ⟨a,ht,hh⟩:=W.1.property.2.1 i
      exact ⟨e a,(het a).trans (congrArg f ht),(heh a).trans (congrArg f hh)⟩,
    by
      obtain ⟨a,ht,hh⟩:=W.1.property.2.2
      exact ⟨k a,(hkt a).trans (congrArg f ht),(hkh a).trans (congrArg f hh)⟩⟩,
    ⟨g W.2.val,hHK _ _ W.2.property.1,fun i=>hH₀ _ _ (W.2.property.2 i)⟩⟩
  inj' W Z he:=by
    have hc:W.1=Z.1:=by
      apply Subtype.ext
      funext i
      exact f.injective (congrArg (fun W=>W.1.val i) he)
    cases W with
    | mk C u=>cases Z with
      | mk D v=>
        dsimp at hc
        subst D
        apply congrArg (Sigma.mk C)
        apply Subtype.ext
        exact g.injective (congrArg (fun W=>W.2.val) he)

theorem markedWheelVertexEmbedding_resources
    (f:V↪V') (g:U↪U') (hcomm:∀ x,f (ρ x)=π (f x))
    (e:E→E') (k:K→K')
    (het:∀ a,tail' (e a)=f (tail a)) (heh:∀ a,head' (e a)=f (head a))
    (hkt:∀ a,ktail' (k a)=f (ktail a)) (hkh:∀ a,khead' (k a)=f (khead a))
    (hH₀:∀ x u,H₀ x u→H₀' (f x) (g u)) (hHK:∀ x u,HK x u→HK' (f x) (g u))
    (W:MarkedWheel tail head ktail khead m ρ b H₀ HK):
    markedWheelPhysicalResources (markedWheelVertexEmbedding f g hcomm e k het heh hkt hkh hH₀ hHK W)=
      (markedWheelPhysicalResources W).image (markedResourceEmbedding f g):=by
  let W':=markedWheelVertexEmbedding f g hcomm e k het heh hkt hkh hH₀ hHK W
  have hr:markedCyclePhysicalEdges tail' head' ktail' khead' m π b W'.1=
      (markedCyclePhysicalEdges tail head ktail khead m ρ b W.1).image (Finset.image f):=by
    unfold markedCyclePhysicalEdges
    rw [Finset.image_image]
    apply Finset.image_congr
    intro i _
    simp only [Function.comp_apply,markedCyclePhysicalEdge_at,W',markedWheelVertexEmbedding,
      Function.Embedding.coeFn_mk,Finset.image_insert,Finset.image_singleton]
    split_ifs <;> simp [hcomm]
  change markedWheelPhysicalResources W'=_
  unfold markedWheelPhysicalResources
  rw [hr,Finset.image_union,Finset.image_image,Finset.image_image,Finset.image_image]
  rfl

theorem markedPackingVertexEmbedding_resources
    (f:V↪V') (g:U↪U') (hcomm:∀ x,f (ρ x)=π (f x))
    (e:E→E') (k:K→K')
    (het:∀ a,tail' (e a)=f (tail a)) (heh:∀ a,head' (e a)=f (head a))
    (hkt:∀ a,ktail' (k a)=f (ktail a)) (hkh:∀ a,khead' (k a)=f (khead a))
    (hH₀:∀ x u,H₀ x u→H₀' (f x) (g u)) (hHK:∀ x u,HK x u→HK' (f x) (g u))
    (M:Finset (MarkedWheel tail head ktail khead m ρ b H₀ HK)):
    (M.image (markedWheelVertexEmbedding f g hcomm e k het heh hkt hkh hH₀ hHK)).biUnion markedWheelPhysicalResources=
      (M.biUnion markedWheelPhysicalResources).image (markedResourceEmbedding f g):=by
  rw [Finset.image_biUnion,Finset.biUnion_image]
  apply Finset.biUnion_congr rfl
  intro W _
  exact markedWheelVertexEmbedding_resources f g hcomm e k het heh hkt hkh hH₀ hHK W

theorem markedPackingVertexEmbedding_matching
    (f:V↪V') (g:U↪U') (hcomm:∀ x,f (ρ x)=π (f x))
    (e:E→E') (k:K→K')
    (het:∀ a,tail' (e a)=f (tail a)) (heh:∀ a,head' (e a)=f (head a))
    (hkt:∀ a,ktail' (k a)=f (ktail a)) (hkh:∀ a,khead' (k a)=f (khead a))
    (hH₀:∀ x u,H₀ x u→H₀' (f x) (g u)) (hHK:∀ x u,HK x u→HK' (f x) (g u))
    (M:Finset (MarkedWheel tail head ktail khead m ρ b H₀ HK))
    (hM:∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)):
    ∀ W∈M.image (markedWheelVertexEmbedding f g hcomm e k het heh hkt hkh hH₀ hHK),
      ∀ Z∈M.image (markedWheelVertexEmbedding f g hcomm e k het heh hkt hkh hH₀ hHK),
      W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z):=by
  intro W hW Z hZ hne
  obtain ⟨W,hMW,rfl⟩:=Finset.mem_image.mp hW
  obtain ⟨Z,hMZ,rfl⟩:=Finset.mem_image.mp hZ
  rw [markedWheelVertexEmbedding_resources,markedWheelVertexEmbedding_resources]
  apply Finset.disjoint_left.mpr
  intro a ha hz
  obtain ⟨x,hx,hxa⟩:=Finset.mem_image.mp ha
  obtain ⟨y,hy,hya⟩:=Finset.mem_image.mp hz
  have hxy:= (markedResourceEmbedding f g).injective (hxa.trans hya.symm)
  exact Finset.disjoint_left.mp (hM W hMW Z hMZ (fun he=>hne (congrArg _ he))) hx (hxy ▸ hy)

end Oberwolfach
