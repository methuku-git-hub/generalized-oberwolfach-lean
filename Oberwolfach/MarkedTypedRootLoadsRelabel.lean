module

public import Oberwolfach.MarkedTypedOccurrenceRelabel
public import Oberwolfach.ResourceRootOmittedRelabel

@[expose] public section
/-! Fixed typed wheel weights and root-omitted loads transport under the
bijections, with both spoke types and directed arc types retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K E' K':Type} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
  [Fintype E] [Fintype K] [Fintype E'] [Fintype K']
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']
  {tail head:E→V} {ktail khead:K→V} {tail' head':E'→V'} {ktail' khead':K'→V'}
  {m b:ℕ} {ρ:Equiv.Perm V} {π:Equiv.Perm V'} {H₀ HK:V→U→Prop} {H₀' HK':V'→U'→Prop}

theorem marked_typed_root_omitted_load_relabel
    (f:V≃V') (g:U≃U') (hcomm:∀ x,f (ρ x)=π (f x))
    (e:E≃E') (k:K≃K')
    (het:∀ a,tail' (e a)=f (tail a)) (heh:∀ a,head' (e a)=f (head a))
    (hkt:∀ a,ktail' (k a)=f (ktail a)) (hkh:∀ a,khead' (k a)=f (khead a))
    (hH₀:∀ x u,H₀ x u↔H₀' (f x) (g u)) (hHK:∀ x u,HK x u↔HK' (f x) (g u))
    (hE:Function.Injective (fun a:E=>(tail a,head a)))
    (hK:Function.Injective (fun a:K=>(ktail a,khead a)))
    (hE':Function.Injective (fun a:E'=>(tail' a,head' a)))
    (hK':Function.Injective (fun a:K'=>(ktail' a,khead' a)))
    (w:MarkedWheel tail' head' ktail' khead' m π b H₀' HK'→ℝ)
    (R:E⊕K→Prop) (R':E'⊕K'→Prop) (H:Bool→V→U→Prop) (H':Bool→V'→U'→Prop)
    (hR:∀ a,R a↔R' (Sum.map e k a)) (hH:∀ j x u,H j x u↔H' j (f x) (g u))
    (root:(E⊕K)⊕(Bool×V×U)) :
    let F:=markedWheelVertexEmbedding (m:=m) (b:=b) f.toEmbedding g.toEmbedding hcomm e k het heh hkt hkh
      (fun x u=>(hH₀ x u).mp) (fun x u=>(hHK x u).mp)
    typedMarkedPotentialLoad (fun W=>w (F W)) R H root =
      typedMarkedPotentialLoad w R' H' (markedTypedResourceEquiv f g e k root) := by
  intro F
  have hs : Function.Surjective F := by
    exact markedWheelVertexEmbedding_surjective (m:=m) (b:=b) f.toEmbedding g.toEmbedding hcomm e k
      e.surjective k.surjective het heh hkt hkh hH₀ hHK
      (fun C i => ⟨f.symm (C.val i), f.apply_symm_apply _⟩)
      (fun W => ⟨g.symm W.2.val, g.apply_symm_apply _⟩)
  let ei := Equiv.ofBijective F ⟨F.injective,hs⟩
  let ea := markedTypedResourceEquiv f g e k
  have hocc : ∀ W, typedMarkedOccurrenceResources (ei W) = (typedMarkedOccurrenceResources W).image ea := by
    intro W
    change typedMarkedOccurrenceResources (F W) = (typedMarkedOccurrenceResources W).image ea
    exact marked_typed_occurrence_image_relabel f g hcomm e k het heh hkt hkh
      (fun x u=>(hH₀ x u).mp) (fun x u=>(hHK x u).mp) hE hK hE' hK' W
  have hk : ∀ a : (E⊕K)⊕(Bool×V×U),
      Sum.elim R (fun jvu=>H jvu.1 jvu.2.1 jvu.2.2) a ↔
      Sum.elim R' (fun jvu=>H' jvu.1 jvu.2.1 jvu.2.2) (ea a) := by
    intro a
    cases a with
    | inl a => exact hR a
    | inr a => rcases a with ⟨j,x,u⟩; exact hH j x u
  exact resource_root_omitted_load_relabel ei ea typedMarkedOccurrenceResources typedMarkedOccurrenceResources
    hocc w (Sum.elim R (fun jvu=>H jvu.1 jvu.2.1 jvu.2.2))
    (Sum.elim R' (fun jvu=>H' jvu.1 jvu.2.1 jvu.2.2)) hk root
end Oberwolfach
