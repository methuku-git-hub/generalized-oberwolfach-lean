module

public import Oberwolfach.EmbeddedTuplePredicates
public import Oberwolfach.CommonMarkedPathConstraintCounts

@[expose] public section

/-! Transport common marked cycles and root-omitted paths through a fixed
vertex embedding. Both typed arc relations are compared at their actual
endpoints; no physical-injectivity premise is imposed on a larger universe. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W V Z U E K E' K':Type*}
  {tail head:E→W} {ktail khead:K→W} {tail' head':E'→V} {ktail' khead':K'→V}
  {m b:ℕ} {ρ:Equiv.Perm W} {π:Equiv.Perm V}

theorem markedCycle_endpoint_transport_iff (f:W↪V) (hcomm:∀ x,f (ρ x)=π (f x))
    (hE:∀ x y,(∃ e,tail e=x∧head e=y)↔(∃ e,tail' e=f x∧head' e=f y))
    (hK:∀ x y,(∃ e,ktail e=x∧khead e=y)↔(∃ e,ktail' e=f x∧khead' e=f y)) (z:Fin (m+1)→W):
    IsMarkedCycleTuple tail head ktail khead m ρ b z↔
      IsMarkedCycleTuple tail' head' ktail' khead' m π b (f∘z):=by
  simp only [IsMarkedCycleTuple,permutationSeparated_embedding_iff f ρ π hcomm,
    Function.comp_apply,hE,hK]

theorem tuple_embedding_insertNth (f:W↪V) (i:Fin (m+1)) (x:W) (z:Fin m→W):
    f∘Fin.insertNth (α:=fun _=>W) i x z=Fin.insertNth (α:=fun _=>V) i (f x) (f∘z):=by
  funext a
  by_cases ha:a=i
  · subst a;simp only [Function.comp_apply,Fin.insertNth_apply_same]
  · obtain ⟨k,rfl⟩:=Fin.exists_succAbove_eq ha
    simp only [Function.comp_apply,Fin.insertNth_apply_succAbove]

theorem commonMarkedCycle_vertex_card [Fintype W] [Fintype V]
    (f:W↪V) (g:Z↪U) (hcomm:∀ x,f (ρ x)=π (f x))
    (hE:∀ x y,(∃ e,tail e=x∧head e=y)↔(∃ e,tail' e=f x∧head' e=f y))
    (hK:∀ x y,(∃ e,ktail e=x∧khead e=y)↔(∃ e,ktail' e=f x∧khead' e=f y))
    (H₀ HK:W→Z→Prop) (H₀' HK':V→U→Prop)
    (hH₀:∀ x u,H₀ x u↔H₀' (f x) (g u)) (hHK:∀ x u,HK x u↔HK' (f x) (g u))
    (u u':Z)
    (hrange:∀ C:CommonMarkedCycle tail' head' ktail' khead' m π b H₀' HK' (g u) (g u'),
      ∀ i,C.val.val i∈Set.range f):
    Fintype.card (CommonMarkedCycle tail head ktail khead m ρ b H₀ HK u u')=
      Fintype.card (CommonMarkedCycle tail' head' ktail' khead' m π b H₀' HK' (g u) (g u')):=by
  let P:=fun z:Fin (m+1)→V=>IsMarkedCycleTuple tail' head' ktail' khead' m π b z∧
    MarkedHubCompatible H₀' HK' z (g u)∧MarkedHubCompatible H₀' HK' z (g u')
  let Q:=fun z:Fin (m+1)→W=>IsMarkedCycleTuple tail head ktail khead m ρ b z∧
    MarkedHubCompatible H₀ HK z u∧MarkedHubCompatible H₀ HK z u'
  have he:=embedded_tuple_predicate_card f P Q (by
    intro z
    simp only [P,Q,markedCycle_endpoint_transport_iff f hcomm hE hK,
      MarkedHubCompatible,Function.comp_apply,hH₀,hHK]) (by
    intro z hz i
    exact hrange ⟨⟨z,hz.1⟩,hz.2⟩ i)
  rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (IsMarkedCycleTuple tail head ktail khead m ρ b)
    (fun C=>MarkedHubCompatible H₀ HK C u∧MarkedHubCompatible H₀ HK C u')),
    Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (IsMarkedCycleTuple tail' head' ktail' khead' m π b)
    (fun C=>MarkedHubCompatible H₀' HK' C (g u)∧MarkedHubCompatible H₀' HK' C (g u')))]
  simp only [Fintype.card_eq_nat_card] at he ⊢
  exact he

theorem canonicalCommonMarkedPath_vertex_card [Fintype W] [Fintype V]
    (f:W↪V) (g:Z↪U) (hcomm:∀ x,f (ρ x)=π (f x))
    (hE:∀ x y,(∃ e,tail e=x∧head e=y)↔(∃ e,tail' e=f x∧head' e=f y))
    (hK:∀ x y,(∃ e,ktail e=x∧khead e=y)↔(∃ e,ktail' e=f x∧khead' e=f y))
    (H₀ HK:W→Z→Prop) (H₀' HK':V→U→Prop)
    (hH₀:∀ x u,H₀ x u↔H₀' (f x) (g u)) (hHK:∀ x u,HK x u↔HK' (f x) (g u))
    (i:Fin (m+1)) (x x':W) (u u':Z)
    (hrange:∀ z:CanonicalCommonMarkedPath tail' head' ktail' khead' m π b H₀' HK' i (f x) (f x') (g u) (g u'),
      ∀ a,z.val a∈Set.range f):
    Fintype.card (CanonicalCommonMarkedPath tail head ktail khead m ρ b H₀ HK i x x' u u')=
      Fintype.card (CanonicalCommonMarkedPath tail' head' ktail' khead' m π b H₀' HK' i (f x) (f x') (g u) (g u')):=by
  let P:=fun z:Fin m→V=>
    IsMarkedCycleTuple tail' head' ktail' khead' m π b (Fin.insertNth i (f x) z)∧
    IsMarkedCycleTuple tail' head' ktail' khead' m π b (Fin.insertNth i (f x') z)∧
    ∀ a:Fin m,(if markedPositionType (i.succAbove a) then HK' (z a) (g u) else H₀' (z a) (g u))∧
      (if markedPositionType (i.succAbove a) then HK' (z a) (g u') else H₀' (z a) (g u'))
  let Q:=fun z:Fin m→W=>
    IsMarkedCycleTuple tail head ktail khead m ρ b (Fin.insertNth i x z)∧
    IsMarkedCycleTuple tail head ktail khead m ρ b (Fin.insertNth i x' z)∧
    ∀ a:Fin m,(if markedPositionType (i.succAbove a) then HK (z a) u else H₀ (z a) u)∧
      (if markedPositionType (i.succAbove a) then HK (z a) u' else H₀ (z a) u')
  have he:=embedded_tuple_predicate_card f P Q (by
    intro z
    have h1:=markedCycle_endpoint_transport_iff (m:=m) (b:=b) f hcomm hE hK (Fin.insertNth i x z)
    have h2:=markedCycle_endpoint_transport_iff (m:=m) (b:=b) f hcomm hE hK (Fin.insertNth i x' z)
    rw [tuple_embedding_insertNth] at h1 h2
    simp only [P,Q,h1,h2,Function.comp_apply,hH₀,hHK]) (by
    intro z hz a;exact hrange ⟨z,hz⟩ a)
  simp only [Fintype.card_eq_nat_card] at he ⊢
  exact he

end Oberwolfach
