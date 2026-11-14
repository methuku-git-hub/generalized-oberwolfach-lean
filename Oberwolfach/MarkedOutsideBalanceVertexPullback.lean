module

public import Oberwolfach.MarkedOutsideBalance

@[expose] public section

/-! Pull the four outside balance identities back to the actual active
vertex and hub domains. The spoke set is the exact image, so no incidence
at a discarded vertex is silently counted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K:Type} [DecidableEq V] [DecidableEq U]
  [DecidableEq V'] [DecidableEq U'] [DecidableEq E] [DecidableEq K]

theorem marked_outside_balance_vertex_pullback
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop) (HK':V'→U'→Prop)
    (f:V↪V') (g:U↪U') (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ)
    (X:Finset V) (Z:Finset U) (I:Finset V') (J:Finset U')
    (hX:∀ x,f x∈I↔x∈X) (hZ:∀ u,g u∈J↔u∈Z)
    (hHK:∀ z∈S,HK' (f z.1) (g z.2)↔HK z.1 z.2)
    (h:MarkedOutsideBalance (f∘tail) (f∘head) (f∘ktail) (f∘khead) HK'
      A (S.image (Prod.map f g)) m I J):
    MarkedOutsideBalance tail head ktail khead HK A S m X Z:=by
  have hi:Function.Injective (Prod.map f g):=by
    intro a b hab
    exact Prod.ext (f.injective (congrArg Prod.fst hab)) (g.injective (congrArg Prod.snd hab))
  have ht (a:E⊕K):Sum.elim (f∘tail) (f∘ktail) a=f (Sum.elim tail ktail a):=by cases a <;> rfl
  have hh (a:E⊕K):Sum.elim (f∘head) (f∘khead) a=f (Sum.elim head khead a):=by cases a <;> rfl
  have hs (p:V'×U'→Prop):((S.image (Prod.map f g)).filter p).card=
      (S.filter (fun z=>p (f z.1,g z.2))).card:=by
    rw [Finset.filter_image,Finset.card_image_of_injective _ hi]
    rfl
  have htype (p:V×U→Prop) (b:Bool):
      S.filter (fun z=>p z∧(if b then HK' (f z.1) (g z.2) else ¬HK' (f z.1) (g z.2)))=
      S.filter (fun z=>p z∧(if b then HK z.1 z.2 else ¬HK z.1 z.2)):=by
    ext z
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro hz
    rw [hHK z hz]
  simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_image] at hs
  constructor
  · intro v hv
    have hd:=h.directed (f v) (fun hv'=>hv ((hX v).mp hv'))
    simpa only [hh,ht,f.injective.eq_iff] using hd
  · intro v hv
    have hd:=h.row (f v) (fun hv'=>hv ((hX v).mp hv'))
    simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_image] at hd ⊢
    rw [hs] at hd
    simpa only [hh,f.injective.eq_iff] using hd
  · intro v hv
    have hd:=h.marked (f v) (fun hv'=>hv ((hX v).mp hv'))
    simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_image] at hd ⊢
    rw [hs] at hd
    simp only [hh,f.injective.eq_iff] at hd
    have he:=congrArg (fun T:Finset (V×U)=>(T:Set (V×U))) (htype (fun z=>z.1=v) true)
    simp only [Finset.coe_filter,ite_true] at he
    rw [he] at hd
    exact hd
  · intro u hu
    have hd:=h.hub (g u) (fun hu'=>hu ((hZ u).mp hu'))
    simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_image] at hd ⊢
    rw [hs,hs] at hd
    simp only [g.injective.eq_iff] at hd
    have he0:=congrArg (fun T:Finset (V×U)=>(T:Set (V×U))) (htype (fun z=>z.2=u) false)
    have he1:=congrArg (fun T:Finset (V×U)=>(T:Set (V×U))) (htype (fun z=>z.2=u) true)
    simp only [Finset.coe_filter,Bool.false_eq_true,ite_false] at he0
    simp only [Finset.coe_filter,ite_true] at he1
    rw [he0,he1] at hd
    exact hd

end Oberwolfach
