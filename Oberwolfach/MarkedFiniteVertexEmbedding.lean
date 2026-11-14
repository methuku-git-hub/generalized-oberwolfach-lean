module

public import Oberwolfach.MarkedFiniteRemainderTransfer

@[expose] public section

/-! Divisibility under an injective enlargement of the row and hub sets.
All rim occurrence identifiers and their types are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K:Type} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U'] [DecidableEq E] [DecidableEq K]

theorem marked_finite_remainder_vertex_image_divisible
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop) (HK':V'→U'→Prop)
    (f:V↪V') (g:U↪U') (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ)
    (hHK:∀ z∈S,HK' (f z.1) (g z.2)↔HK z.1 z.2)
    (h:MarkedRemainderDivisible tail head ktail khead HK A S m):
    MarkedRemainderDivisible (f∘tail) (f∘head) (f∘ktail) (f∘khead) HK'
      A (S.image (Prod.map f g)) m:=by
  let G:=markedRemainderGraph tail head ktail khead HK A S
  have hh:=IndexedMarkedGraph.map_balanced G m
    (markedRemainderGraph_balanced tail head ktail khead HK A S m h) f g
  have hi:Function.Injective (Prod.map f g):=by
    intro a b hab
    exact Prod.ext (f.injective (congrArg Prod.fst hab)) (g.injective (congrArg Prod.snd hab))
  have hs (p:V'×U'→Prop):((S.image (Prod.map f g)).filter p).card=
      (S.filter (fun z=>p (f z.1,g z.2))).card:=by
    rw [Finset.filter_image,Finset.card_image_of_injective _ hi]
    rfl
  have he (a:E⊕K):Sum.elim (f∘head) (f∘khead) a=f (Sum.elim head khead a):=by cases a <;> rfl
  have ht (a:E⊕K):Sum.elim (f∘tail) (f∘ktail) a=f (Sum.elim tail ktail a):=by cases a <;> rfl
  have hmarked (v:V'):
      S.filter (fun z=>f z.1=v∧HK' (f z.1) (g z.2))=
        S.filter (fun z=>f z.1=v∧HK z.1 z.2):=by
    ext z
    simp only [Finset.mem_filter]
    exact and_congr_right (fun hz=>and_congr_right (fun _=>hHK z hz))
  have hhub (u:U') (b:Bool):
      S.filter (fun z=>g z.2=u∧decide (HK' (f z.1) (g z.2))=b)=
        S.filter (fun z=>g z.2=u∧decide (HK z.1 z.2)=b):=by
    ext z
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro hz
    rw [hHK z hz]
  simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_image] at hs
  constructor
  · intro v
    have hv:=hh.directed v
    change Fintype.card {a:A // f (Sum.elim head khead a.val)=v}=
      Fintype.card {a:A // f (Sum.elim tail ktail a.val)=v} at hv
    rw [marked_finite_filter_card A (fun a=>f (Sum.elim head khead a)=v),
      marked_finite_filter_card A (fun a=>f (Sum.elim tail ktail a)=v)] at hv
    simpa only [←Set.ncard_coe_finset,Finset.coe_filter,he,ht] using hv
  · intro v
    have hv:=hh.row v
    change Fintype.card {a:A // f (Sum.elim head khead a.val)=v}=
      Fintype.card {z:S // f z.val.1=v} at hv
    rw [marked_finite_filter_card A (fun a=>f (Sum.elim head khead a)=v),
      marked_finite_filter_card S (fun z=>f z.1=v)] at hv
    simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_image] at hv ⊢
    rw [hs]
    simpa only [he] using hv
  · intro v
    have hv:=hh.marked v
    change Fintype.card {a:A // f (Sum.elim head khead a.val)=v∧markedArcType a.val=true}=
      Fintype.card {z:S // f z.val.1=v∧decide (HK z.val.1 z.val.2)=true} at hv
    simp only [decide_eq_true_eq] at hv
    rw [marked_finite_filter_card A (fun a=>f (Sum.elim head khead a)=v∧markedArcType a=true),
      marked_finite_filter_card S (fun z=>f z.1=v∧HK z.1 z.2)] at hv
    have hm:=congrArg (fun F:Finset (V×U)=>(F:Set (V×U))) (hmarked v)
    simp only [Finset.coe_filter] at hm
    simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_image] at hv ⊢
    rw [hs,hm]
    simpa only [he] using hv
  · intro u
    have hu:=hh.hub u
    change Fintype.card {z:S // g z.val.2=u∧decide (HK z.val.1 z.val.2)=false}=
      m*Fintype.card {z:S // g z.val.2=u∧decide (HK z.val.1 z.val.2)=true} at hu
    simp only [decide_eq_false_iff_not,decide_eq_true_eq] at hu
    rw [marked_finite_filter_card S (fun z=>g z.2=u∧¬HK z.1 z.2),
      marked_finite_filter_card S (fun z=>g z.2=u∧HK z.1 z.2)] at hu
    have h0:=hhub u false
    have h1:=hhub u true
    simp only [decide_eq_false_iff_not,decide_eq_true_eq] at h0 h1
    have h0':=congrArg (fun F:Finset (V×U)=>(F:Set (V×U))) h0
    have h1':=congrArg (fun F:Finset (V×U)=>(F:Set (V×U))) h1
    simp only [Finset.coe_filter] at h0' h1'
    simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_image] at hu ⊢
    rw [hs,hs,h0',h1']
    exact hu

end Oberwolfach
