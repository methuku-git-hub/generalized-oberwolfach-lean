module

public import Oberwolfach.MarkedFiniteRemainder

@[expose] public section

/-! Transport an actual finite typed remainder along a map preserving its
arc endpoints and types. Counts, four divisibility equations and physical
resources are preserved exactly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem finite_subtype_image_filter_card {A B:Type} [DecidableEq A] [DecidableEq B]
    (S:Finset A) (f:S→B) (hf:Function.Injective f) (p:B→Prop) (q:A→Prop)
    (hp:∀ a:S,p (f a)↔q a.val):
    ((Finset.univ.image f).filter p).card=(S.filter q).card:=by
  rw [Finset.filter_image,Finset.card_image_of_injective _ hf]
  have he:(Finset.univ.filter (fun a:S=>p (f a)))=Finset.univ.filter (fun a:S=>q a.val):=by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hp]
  rw [he]
  exact (Fintype.card_subtype (fun a:S=>q a.val)).symm.trans (marked_finite_filter_card S q)

variable {V U E K E' K':Type} [DecidableEq V] [DecidableEq U]
  [DecidableEq E] [DecidableEq K] [DecidableEq E'] [DecidableEq K']
  {tail head:E→V} {ktail khead:K→V} {tail' head':E'→V} {ktail' khead':K'→V}
  {HK HK':V→U→Prop} {m:ℕ}

theorem marked_physical_edge_eq_of_endpoints_and_type (π:Equiv.Perm V)
    (a:E⊕K) (a':E'⊕K')
    (hs:Sum.elim tail' ktail' a'=Sum.elim tail ktail a)
    (hd:Sum.elim head' khead' a'=Sum.elim head khead a)
    (ht:markedArcType a'=markedArcType a):
    markedPhysicalEdge tail' head' ktail' khead' π a'=markedPhysicalEdge tail head ktail khead π a:=by
  cases a <;> cases a' <;> simp only [markedArcType,Bool.false_eq_true,Bool.true_eq_false] at ht
  all_goals simp only [markedPhysicalEdge,Sum.elim_inl,Sum.elim_inr] at hs hd ⊢
  all_goals rw [hs,hd]

theorem marked_finite_remainder_image_divisible
    (A:Finset (E⊕K)) (S:Finset (V×U)) (f:A→E'⊕K') (hf:Function.Injective f)
    (hs:∀ a,Sum.elim tail' ktail' (f a)=Sum.elim tail ktail a.val)
    (hd:∀ a,Sum.elim head' khead' (f a)=Sum.elim head khead a.val)
    (ht:∀ a,markedArcType (f a)=markedArcType a.val)
    (hHK:∀ z∈S,HK' z.1 z.2↔HK z.1 z.2)
    (h:MarkedRemainderDivisible tail head ktail khead HK A S m):
    MarkedRemainderDivisible tail' head' ktail' khead' HK' (Finset.univ.image f) S m:=by
  have hhead (v:V):((Finset.univ.image f).filter (fun a=>Sum.elim head' khead' a=v)).card=
      (A.filter (fun a=>Sum.elim head khead a=v)).card:=
    by convert finite_subtype_image_filter_card A f hf (fun a=>Sum.elim head' khead' a=v) (fun a=>Sum.elim head khead a=v) (fun a=>by rw [hd]) using 1 <;> congr!
  have htail (v:V):((Finset.univ.image f).filter (fun a=>Sum.elim tail' ktail' a=v)).card=
      (A.filter (fun a=>Sum.elim tail ktail a=v)).card:=
    by convert finite_subtype_image_filter_card A f hf (fun a=>Sum.elim tail' ktail' a=v) (fun a=>Sum.elim tail ktail a=v) (fun a=>by rw [hs]) using 1 <;> congr!
  have hmark (v:V):((Finset.univ.image f).filter (fun a=>Sum.elim head' khead' a=v∧markedArcType a=true)).card=
      (A.filter (fun a=>Sum.elim head khead a=v∧markedArcType a=true)).card:=
    by convert finite_subtype_image_filter_card A f hf (fun a=>Sum.elim head' khead' a=v∧markedArcType a=true) (fun a=>Sum.elim head khead a=v∧markedArcType a=true) (fun a=>by rw [hd,ht]) using 1 <;> congr!
  have hsp (p:V×U→Prop):S.filter (fun z=>p z∧HK' z.1 z.2)=S.filter (fun z=>p z∧HK z.1 z.2):=by
    ext z
    simp only [Finset.mem_filter]
    exact and_congr_right (fun hz=>and_congr_right (fun _=>hHK z hz))
  have hsp0 (p:V×U→Prop):S.filter (fun z=>p z∧¬HK' z.1 z.2)=S.filter (fun z=>p z∧¬HK z.1 z.2):=by
    ext z
    simp only [Finset.mem_filter]
    exact and_congr_right (fun hz=>and_congr_right (fun _=>not_congr (hHK z hz)))
  constructor
  · intro v
    exact (hhead v).trans ((h.directed v).trans (htail v).symm)
  · intro v
    exact (hhead v).trans (h.row v)
  · intro v
    calc
      _ = (A.filter (fun a=>Sum.elim head khead a=v∧markedArcType a=true)).card:=hmark v
      _ = (S.filter (fun s=>s.1=v∧HK s.1 s.2)).card:=h.marked v
      _ = _:=by convert (congrArg Finset.card (hsp (fun z=>z.1=v))).symm using 1 <;> congr!
  · intro u
    calc
      _ = (S.filter (fun s=>s.2=u∧¬HK s.1 s.2)).card:=by
        convert congrArg Finset.card (hsp0 (fun z=>z.2=u)) using 1 <;> congr!
      _ = m*(S.filter (fun s=>s.2=u∧HK s.1 s.2)).card:=h.hub u
      _ = _:=by convert (congrArg (fun T:Finset (V×U)=>m*T.card) (hsp (fun z=>z.2=u))).symm using 1 <;> congr!

theorem marked_finite_remainder_map_injective (π:Equiv.Perm V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (A:Finset (E⊕K)) (f:A→E'⊕K')
    (hs:∀ a,Sum.elim tail' ktail' (f a)=Sum.elim tail ktail a.val)
    (hd:∀ a,Sum.elim head' khead' (f a)=Sum.elim head khead a.val)
    (ht:∀ a,markedArcType (f a)=markedArcType a.val):Function.Injective f:=by
  intro a z he
  apply Subtype.ext
  apply hp
  exact (marked_physical_edge_eq_of_endpoints_and_type π a.val (f a) (hs a) (hd a) (ht a)).symm.trans
    ((congrArg (markedPhysicalEdge tail' head' ktail' khead' π) he).trans
      (marked_physical_edge_eq_of_endpoints_and_type π z.val (f z) (hs z) (hd z) (ht z)))

theorem marked_finite_remainder_image_resources (π:Equiv.Perm V)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (f:A→E'⊕K')
    (hs:∀ a,Sum.elim tail' ktail' (f a)=Sum.elim tail ktail a.val)
    (hd:∀ a,Sum.elim head' khead' (f a)=Sum.elim head khead a.val)
    (ht:∀ a,markedArcType (f a)=markedArcType a.val):
    (Finset.univ.image f).image (fun a=>Sum.inl (β:=V×U) (markedPhysicalEdge tail' head' ktail' khead' π a))∪S.image Sum.inr=
      A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr:=by
  congr 1
  rw [Finset.image_image]
  ext e
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  have he (a:A):markedPhysicalEdge tail' head' ktail' khead' π (f a)=markedPhysicalEdge tail head ktail khead π a.val:=
    marked_physical_edge_eq_of_endpoints_and_type π a.val (f a) (hs a) (hd a) (ht a)
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a.val,a.property,by simpa only [Function.comp_apply,he] using ha⟩
  · rintro ⟨a,ha,heq⟩
    exact ⟨⟨a,ha⟩,by simpa only [Function.comp_apply,he] using heq⟩

end Oberwolfach
