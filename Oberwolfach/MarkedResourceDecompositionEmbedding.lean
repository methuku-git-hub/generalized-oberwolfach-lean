module

public import Oberwolfach.ResourceEmbeddingDecompositions
public import Oberwolfach.MarkedWheelVertexEmbedding

@[expose] public section

/-! Exact decompositions embed along permutation-compatible vertex and hub
maps and type-preserving arc maps. The covered physical set is transported
by the same injective resource map as the individual wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K E' K':Type} [DecidableEq V] [DecidableEq U]
  [DecidableEq V'] [DecidableEq U']
  {tail head:E → V} {ktail khead:K → V} {tail' head':E' → V'} {ktail' khead':K' → V'}
  {m b:ℕ} {ρ:Equiv.Perm V} {π:Equiv.Perm V'} {H₀ HK:V → U → Prop} {H₀' HK':V' → U' → Prop}

theorem marked_resource_decomposition_embedding
    (f:V↪V') (g:U↪U') (hcomm:∀ x,f (ρ x)=π (f x))
    (e:E → E') (k:K → K')
    (het:∀ a,tail' (e a)=f (tail a)) (heh:∀ a,head' (e a)=f (head a))
    (hkt:∀ a,ktail' (k a)=f (ktail a)) (hkh:∀ a,khead' (k a)=f (khead a))
    (hH₀:∀ x u,H₀ x u → H₀' (f x) (g u)) (hHK:∀ x u,HK x u → HK' (f x) (g u))
    (S:Finset (Finset V⊕(V×U)))
    (hS:HasResourceDecomposition
      (fun W:MarkedWheel tail head ktail khead m ρ b H₀ HK=>markedWheelPhysicalResources W) S):
    HasResourceDecomposition
      (fun W:MarkedWheel tail' head' ktail' khead' m π b H₀' HK'=>markedWheelPhysicalResources W)
      (S.image (markedResourceEmbedding f g)):=by
  exact resource_decomposition_embedding _ _ (markedResourceEmbedding f g)
    (markedWheelVertexEmbedding f g hcomm e k het heh hkt hkh hH₀ hHK)
    (markedResourceEmbedding f g).injective
    (markedWheelVertexEmbedding_resources f g hcomm e k het heh hkt hkh hH₀ hHK) S hS

end Oberwolfach
