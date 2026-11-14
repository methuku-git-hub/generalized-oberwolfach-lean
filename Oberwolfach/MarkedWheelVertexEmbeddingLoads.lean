module

public import Oberwolfach.MarkedWheelVertexEmbeddingSurjective

@[expose] public section

/-! Exact rim and spoke loads under a bijective representation of the same
supported wheels on smaller row and hub domains. No weights are recomputed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K E' K':Type} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']
  {tail head:E→V} {ktail khead:K→V} {tail' head':E'→V'} {ktail' khead':K'→V'}
  {m b:ℕ} {ρ:Equiv.Perm V} {π:Equiv.Perm V'} {H₀ HK:V→U→Prop} {H₀' HK':V'→U'→Prop}

theorem markedCycleIncidence_vertex_embedding
    (f:V↪V') (e:E→E') (k:K→K')
    (het:∀ a,tail' (e a)=f (tail a)) (heh:∀ a,head' (e a)=f (head a))
    (hkt:∀ a,ktail' (k a)=f (ktail a)) (hkh:∀ a,khead' (k a)=f (khead a))
    (C:Fin (m+1)→V) (a:E⊕K):
    markedCycleIncidence tail' head' ktail' khead' m (f∘C) (Sum.map e k a)=
      markedCycleIncidence tail head ktail khead m C a:=by
  cases a <;>
    simp only [markedCycleIncidence,Sum.map_inl,Sum.map_inr,Sum.elim_inl,Sum.elim_inr,
      directedEdgeIndicator,Function.comp_apply,het,heh,hkt,hkh,f.injective.eq_iff]

theorem markedWheelVertexEmbedding_loads
    (f:V↪V') (g:U↪U') (hcomm:∀ x,f (ρ x)=π (f x))
    (e:E→E') (k:K→K')
    (het:∀ a,tail' (e a)=f (tail a)) (heh:∀ a,head' (e a)=f (head a))
    (hkt:∀ a,ktail' (k a)=f (ktail a)) (hkh:∀ a,khead' (k a)=f (khead a))
    (hH₀:∀ x u,H₀ x u→H₀' (f x) (g u)) (hHK:∀ x u,HK x u→HK' (f x) (g u))
    (hsurj:Function.Surjective (markedWheelVertexEmbedding (m:=m) (b:=b) f g hcomm e k het heh hkt hkh hH₀ hHK))
    (w:MarkedWheel tail' head' ktail' khead' m π b H₀' HK'→ℝ):
    let F:=markedWheelVertexEmbedding (m:=m) (b:=b) f g hcomm e k het heh hkt hkh hH₀ hHK
    (∀ a:E⊕K,markedWheelRimLoad (fun W=>w (F W)) a=markedWheelRimLoad w (Sum.map e k a))∧
    (∀ j v u,markedWheelSpokeLoad (fun W=>w (F W)) j v u=markedWheelSpokeLoad w j (f v) (g u)):=by
  intro F
  let eqv:=Equiv.ofBijective F ⟨F.injective,hsurj⟩
  constructor
  · intro a
    have hh:=eqv.sum_comp (fun W=>w W*markedCycleIncidence tail' head' ktail' khead' m W.1.val (Sum.map e k a))
    change _=markedWheelRimLoad w (Sum.map e k a) at hh
    rw [←hh]
    unfold markedWheelRimLoad
    apply Finset.sum_congr rfl
    intro W _
    change w (F W)*markedCycleIncidence tail head ktail khead m W.1.val a=
      w (F W)*markedCycleIncidence tail' head' ktail' khead' m (f∘W.1.val) (Sum.map e k a)
    rw [markedCycleIncidence_vertex_embedding f e k het heh hkt hkh]
  · intro j v u
    have hh:=eqv.sum_comp (fun W=>w W*(if W.2.val=g u then markedSpokeIndicator W.1.val j (f v) else 0))
    change _=markedWheelSpokeLoad w j (f v) (g u) at hh
    rw [←hh]
    unfold markedWheelSpokeLoad
    apply Finset.sum_congr rfl
    intro W _
    change w (F W)*(if W.2.val=u then markedSpokeIndicator W.1.val j v else 0)=
      w (F W)*(if g W.2.val=g u then markedSpokeIndicator (f∘W.1.val) j (f v) else 0)
    simp only [g.injective.eq_iff,markedSpokeIndicator,Function.comp_apply,f.injective.eq_iff]

end Oberwolfach
