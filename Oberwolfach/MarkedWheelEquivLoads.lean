module

public import Oberwolfach.MarkedWheelVertexEmbeddingLoads

@[expose] public section
/-! Bijective row, hub and typed-arc maps transport every supported wheel and
its fixed weights and loads; no new weights or physical identifications are
introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K E' K':Type} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']
  {tail head:E→V} {ktail khead:K→V} {tail' head':E'→V'} {ktail' khead':K'→V'}
  {m b:ℕ} {ρ:Equiv.Perm V} {π:Equiv.Perm V'} {H₀ HK:V→U→Prop} {H₀' HK':V'→U'→Prop}

theorem marked_wheel_equiv_loads
    (f:V≃V') (g:U≃U') (hcomm:∀ x,f (ρ x)=π (f x))
    (e:E≃E') (k:K≃K')
    (het:∀ a,tail' (e a)=f (tail a)) (heh:∀ a,head' (e a)=f (head a))
    (hkt:∀ a,ktail' (k a)=f (ktail a)) (hkh:∀ a,khead' (k a)=f (khead a))
    (hH₀:∀ x u,H₀ x u↔H₀' (f x) (g u)) (hHK:∀ x u,HK x u↔HK' (f x) (g u))
    (w:MarkedWheel tail' head' ktail' khead' m π b H₀' HK'→ℝ):
    let F:=markedWheelVertexEmbedding (m:=m) (b:=b) f.toEmbedding g.toEmbedding hcomm e k het heh hkt hkh
      (fun x u=>(hH₀ x u).mp) (fun x u=>(hHK x u).mp)
    (∀ a:E⊕K,markedWheelRimLoad (fun W=>w (F W)) a=markedWheelRimLoad w (Sum.map e k a)) ∧
    (∀ j v u,markedWheelSpokeLoad (fun W=>w (F W)) j v u=markedWheelSpokeLoad w j (f v) (g u)) := by
  have hs := markedWheelVertexEmbedding_surjective (m:=m) (b:=b) f.toEmbedding g.toEmbedding hcomm e k
    e.surjective k.surjective het heh hkt hkh hH₀ hHK
    (fun C i => ⟨f.symm (C.val i), f.apply_symm_apply _⟩)
    (fun W => ⟨g.symm W.2.val, g.apply_symm_apply _⟩)
  exact markedWheelVertexEmbedding_loads f.toEmbedding g.toEmbedding hcomm e k het heh hkt hkh
    (fun x u=>(hH₀ x u).mp) (fun x u=>(hHK x u).mp) hs w
end Oberwolfach
