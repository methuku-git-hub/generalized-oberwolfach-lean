module

public import Oberwolfach.MarkedFiniteBalanceEmbedding

@[expose] public section

/-! Opposite-endpoint balances commute with injective vertex and occurrence
maps when both domains are their exact preimages. This preserves the original
ambient root in each comparison and does not enlarge any uniform event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K E' K':Type}
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']
  [DecidableEq E] [DecidableEq K] [DecidableEq E'] [DecidableEq K']

theorem markedFiniteDomainBalance_embedding
    (tail head:E→V) (ktail khead:K→V) (tail' head':E'→V') (ktail' khead':K'→V')
    (HK:V→U→Prop) (HK':V'→U'→Prop) (f:V↪V') (g:U↪U') (e:E↪E') (k:K↪K')
    (het:∀ a,tail' (e a)=f (tail a)) (heh:∀ a,head' (e a)=f (head a))
    (hkt:∀ a,ktail' (k a)=f (ktail a)) (hkh:∀ a,khead' (k a)=f (khead a))
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ)
    (hHK:∀ s∈S,HK' (f s.1) (g s.2)↔HK s.1 s.2)
    (X:Finset V) (Z:Finset U) (I:Finset V') (J:Finset U')
    (hX:∀ x,f x∈I↔x∈X) (hZ:∀ u,g u∈J↔u∈Z) (z:V⊕U) (i:Fin 4):
    markedFiniteDomainBalance tail' head' ktail' khead' HK' (A.image (e.sumMap k))
      (S.image (Prod.map f g)) m I J (Sum.map f g z) i=
      markedFiniteDomainBalance tail head ktail khead HK A S m X Z z i:=by
  have ht (a:E⊕K):Sum.elim tail' ktail' ((e.sumMap k) a)=f (Sum.elim tail ktail a):=by
    cases a with
    | inl a=>exact het a
    | inr a=>exact hkt a
  have hh (a:E⊕K):Sum.elim head' khead' ((e.sumMap k) a)=f (Sum.elim head khead a):=by
    cases a with
    | inl a=>exact heh a
    | inr a=>exact hkh a
  cases z with
  | inl v=>
    have hA:((A.image (e.sumMap k)).filter
        (fun a=>(if Sum.elim tail' ktail' a=f v then Sum.elim head' khead' a else Sum.elim tail' ktail' a)∈I))=
        (A.filter (fun a=>(if Sum.elim tail ktail a=v then Sum.elim head khead a else Sum.elim tail ktail a)∈X)).image (e.sumMap k):=by
      rw [Finset.filter_image]
      congr 1
      apply Finset.filter_congr
      intro a _
      simp only [ht,hh,f.injective.eq_iff]
      split_ifs <;> exact hX _
    have hS:((S.image (Prod.map f g)).filter (fun s=>s.2∈J))=
        (S.filter (fun s=>s.2∈Z)).image (Prod.map f g):=by
      rw [Finset.filter_image]
      congr 1
      apply Finset.filter_congr
      intro s _
      exact hZ s.2
    simp only [Sum.map_inl,Sum.map_inr]
    dsimp only [markedFiniteDomainBalance]
    rw [hA,hS]
    exact markedFiniteBalance_embedding tail head ktail khead tail' head' ktail' khead' HK HK' f g e k
      het heh hkt hkh _ _ m (fun s hs=>hHK s (Finset.mem_filter.mp hs).1) (Sum.inl v) i
  | inr u=>
    have hS:((S.image (Prod.map f g)).filter (fun s=>s.1∈I))=
        (S.filter (fun s=>s.1∈X)).image (Prod.map f g):=by
      rw [Finset.filter_image]
      congr 1
      apply Finset.filter_congr
      intro s _
      exact hX s.1
    simp only [Sum.map_inl,Sum.map_inr]
    dsimp only [markedFiniteDomainBalance]
    rw [hS]
    have h:=markedFiniteBalance_embedding tail head ktail khead tail' head' ktail' khead' HK HK' f g e k
      het heh hkt hkh ∅ (S.filter (fun s=>s.1∈X)) m
      (fun s hs=>hHK s (Finset.mem_filter.mp hs).1) (Sum.inr u) i
    simpa only [Finset.image_empty,Sum.map_inr] using h

end Oberwolfach
