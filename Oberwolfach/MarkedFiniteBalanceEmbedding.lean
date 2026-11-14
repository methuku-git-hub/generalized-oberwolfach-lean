module

public import Oberwolfach.MarkedFiniteDomainBalance

@[expose] public section

/-! The actual finite balance values are invariant under injective maps
of typed arcs, rows and hubs. Only mapped roots are compared, and the
marked spoke predicate agrees on the supplied spoke set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K E' K':Type}
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']
  [DecidableEq E] [DecidableEq K] [DecidableEq E'] [DecidableEq K']

theorem markedFiniteBalance_embedding
    (tail head:E→V) (ktail khead:K→V) (tail' head':E'→V') (ktail' khead':K'→V')
    (HK:V→U→Prop) (HK':V'→U'→Prop) (f:V↪V') (g:U↪U') (e:E↪E') (k:K↪K')
    (het:∀ a,tail' (e a)=f (tail a)) (heh:∀ a,head' (e a)=f (head a))
    (hkt:∀ a,ktail' (k a)=f (ktail a)) (hkh:∀ a,khead' (k a)=f (khead a))
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ)
    (hHK:∀ z∈S,HK' (f z.1) (g z.2)↔HK z.1 z.2) (z:V⊕U) (i:Fin 4):
    markedFiniteBalance tail' head' ktail' khead' HK' (A.image (e.sumMap k))
      (S.image (Prod.map f g)) m (Sum.map f g z) i=
      markedFiniteBalance tail head ktail khead HK A S m z i:=by
  have ha (p:E'⊕K'→Prop):((A.image (e.sumMap k)).filter p).card=
      (A.filter (fun a=>p ((e.sumMap k) a))).card:=by
    rw [Finset.filter_image,Finset.card_image_of_injective _ (e.sumMap k).injective]
  have hfg:Function.Injective (Prod.map f g):=by
    intro a b hab
    exact Prod.ext (f.injective (congrArg Prod.fst hab)) (g.injective (congrArg Prod.snd hab))
  have hs (p:V'×U'→Prop):((S.image (Prod.map f g)).filter p).card=
      (S.filter (fun s=>p (f s.1,g s.2))).card:=by
    rw [Finset.filter_image,Finset.card_image_of_injective _ hfg];rfl
  have ht (a:E⊕K):Sum.elim tail' ktail' ((e.sumMap k) a)=f (Sum.elim tail ktail a):=by
    cases a with
    | inl a=>exact het a
    | inr a=>exact hkt a
  have hh (a:E⊕K):Sum.elim head' khead' ((e.sumMap k) a)=f (Sum.elim head khead a):=by
    cases a with
    | inl a=>exact heh a
    | inr a=>exact hkh a
  have hm (a:E⊕K):markedArcType ((e.sumMap k) a)=markedArcType a:=by cases a <;> rfl
  have htype (p:V×U→Prop) (b:Bool):
      S.filter (fun s=>p s∧(if b then HK' (f s.1) (g s.2) else ¬HK' (f s.1) (g s.2)))=
      S.filter (fun s=>p s∧(if b then HK s.1 s.2 else ¬HK s.1 s.2)):=by
    ext s;simp only [Finset.mem_filter]
    apply and_congr_right;intro hs;rw [hHK s hs]
  simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_image] at ha hs
  cases z with
  | inl v=>
    have hk:=congrArg (fun F:Finset (V×U)=>(F:Set (V×U))) (htype (fun s=>s.1=v) true)
    simp only [Finset.coe_filter,ite_true] at hk
    fin_cases i <;> simp only [Sum.map_inl,markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
      (try simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_image]) <;>
      (try rw [ha]) <;> (try rw [hs]) <;>
      simp only [ht,hh,hm,f.injective.eq_iff,hk]
  | inr u=>
    have hk:=congrArg (fun F:Finset (V×U)=>(F:Set (V×U))) (htype (fun s=>s.2=u) true)
    have h0:=congrArg (fun F:Finset (V×U)=>(F:Set (V×U))) (htype (fun s=>s.2=u) false)
    simp only [Finset.coe_filter,ite_true] at hk
    simp only [Finset.coe_filter,Bool.false_eq_true,ite_false] at h0
    fin_cases i <;> simp only [Sum.map_inr,markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
      (try simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_image]) <;>
      (try rw [hs,hs]) <;> simp only [g.injective.eq_iff,hk,h0]

end Oberwolfach
