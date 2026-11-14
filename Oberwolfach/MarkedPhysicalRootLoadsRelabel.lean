module

public import Oberwolfach.MarkedWheelEquivLoads
public import Oberwolfach.MarkedPhysicalResourceEquiv
public import Oberwolfach.ResourceRootOmittedRelabel

@[expose] public section
/-! A fixed weight and an omitted physical root are transported through a
bijection of actual marked wheels and physical resources. This statement is
about physical resources; it does not identify the two typed spoke relations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K E' K':Type} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']
  {tail head:E→V} {ktail khead:K→V} {tail' head':E'→V'} {ktail' khead':K'→V'}
  {m b:ℕ} {ρ:Equiv.Perm V} {π:Equiv.Perm V'} {H₀ HK:V→U→Prop} {H₀' HK':V'→U'→Prop}

theorem marked_physical_root_omitted_load_relabel
    (f:V≃V') (g:U≃U') (hcomm:∀ x,f (ρ x)=π (f x))
    (e:E≃E') (k:K≃K')
    (het:∀ a,tail' (e a)=f (tail a)) (heh:∀ a,head' (e a)=f (head a))
    (hkt:∀ a,ktail' (k a)=f (ktail a)) (hkh:∀ a,khead' (k a)=f (khead a))
    (hH₀:∀ x u,H₀ x u↔H₀' (f x) (g u)) (hHK:∀ x u,HK x u↔HK' (f x) (g u))
    (w:MarkedWheel tail' head' ktail' khead' m π b H₀' HK'→ℝ)
    (keep : (Finset V' ⊕ (V'×U')) → Prop) (root : Finset V ⊕ (V×U)) :
    let F:=markedWheelVertexEmbedding (m:=m) (b:=b) f.toEmbedding g.toEmbedding hcomm e k het heh hkt hkh
      (fun x u=>(hH₀ x u).mp) (fun x u=>(hHK x u).mp)
    resourceRootOmittedLoad markedWheelPhysicalResources (fun W=>w (F W))
      (fun a=>keep (markedPhysicalResourceEquiv f g a)) root =
    resourceRootOmittedLoad markedWheelPhysicalResources w keep (markedPhysicalResourceEquiv f g root) := by
  intro F
  have hs : Function.Surjective F := by
    exact markedWheelVertexEmbedding_surjective (m:=m) (b:=b) f.toEmbedding g.toEmbedding hcomm e k
      e.surjective k.surjective het heh hkt hkh hH₀ hHK
      (fun C i => ⟨f.symm (C.val i), f.apply_symm_apply _⟩)
      (fun W => ⟨g.symm W.2.val, g.apply_symm_apply _⟩)
  let ei := Equiv.ofBijective F ⟨F.injective,hs⟩
  let ea := markedPhysicalResourceEquiv f g
  have hemap : (ea : Finset V⊕(V×U) → Finset V'⊕(V'×U')) =
      markedResourceEmbedding f.toEmbedding g.toEmbedding := by
    funext a
    exact marked_physical_resource_equiv_apply f g a
  have hR : ∀ W, markedWheelPhysicalResources (ei W) = (markedWheelPhysicalResources W).image ea := by
    intro W
    change markedWheelPhysicalResources (F W) = (markedWheelPhysicalResources W).image ea
    rw [hemap]
    exact markedWheelVertexEmbedding_resources f.toEmbedding g.toEmbedding hcomm e k het heh hkt hkh
      (fun x u=>(hH₀ x u).mp) (fun x u=>(hHK x u).mp) W
  exact resource_root_omitted_load_relabel ei ea markedWheelPhysicalResources markedWheelPhysicalResources
    hR w (fun a=>keep (ea a)) keep (fun _=>Iff.rfl) root
end Oberwolfach
