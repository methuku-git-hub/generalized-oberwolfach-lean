module

public import Oberwolfach.IndexedMarkedActiveGraph

@[expose] public section

/-! A finite remainder in the actual typed host, with its unchanged edge
occurrences and physical resource set. Its divisibility equations are
exactly the four balances used by the marked absorber construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

def markedArcType : E⊕K→Bool
  | .inl _=>false
  | .inr _=>true

def markedRemainderGraph (tail head:E→V) (ktail khead:K→V)
    (HK:V→U→Prop) (A:Finset (E⊕K)) (S:Finset (V×U)):
    IndexedMarkedGraph V U A S where
  src a:=Sum.elim tail ktail a.val
  dst a:=Sum.elim head khead a.val
  row s:=s.val.1
  hub s:=s.val.2
  jr a:=markedArcType a.val
  js s:=decide (HK s.val.1 s.val.2)

structure MarkedRemainderDivisible (tail head:E→V) (ktail khead:K→V)
    (HK:V→U→Prop) (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ):Prop where
  directed:∀ v,(A.filter (fun a=>Sum.elim head khead a=v)).card=
    (A.filter (fun a=>Sum.elim tail ktail a=v)).card
  row:∀ v,(A.filter (fun a=>Sum.elim head khead a=v)).card=
    (S.filter (fun s=>s.1=v)).card
  marked:∀ v,(A.filter (fun a=>Sum.elim head khead a=v∧markedArcType a=true)).card=
    (S.filter (fun s=>s.1=v∧HK s.1 s.2)).card
  hub:∀ u,(S.filter (fun s=>s.2=u∧¬HK s.1 s.2)).card=
    m*(S.filter (fun s=>s.2=u∧HK s.1 s.2)).card

theorem marked_finite_filter_card {X:Type} (T:Finset X) (p:X→Prop) [Fintype {x:T // p x.val}]:
    Fintype.card {x:T // p x.val}=(T.filter p).card:=by
  let e:{x:T // p x.val}≃(T.filter p):=
    { toFun:=fun x=>⟨x.val.val,Finset.mem_filter.mpr ⟨x.val.property,x.property⟩⟩
      invFun:=fun x=>⟨⟨x.val,(Finset.mem_filter.mp x.property).1⟩,(Finset.mem_filter.mp x.property).2⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

theorem markedRemainderGraph_balanced
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ)
    (h:MarkedRemainderDivisible tail head ktail khead HK A S m):
    (markedRemainderGraph tail head ktail khead HK A S).IsBalanced m:=by
  constructor
  · intro v
    change Fintype.card {a:A // Sum.elim head khead a.val=v}=Fintype.card {a:A // Sum.elim tail ktail a.val=v}
    rw [marked_finite_filter_card A (fun a=>Sum.elim head khead a=v),marked_finite_filter_card A (fun a=>Sum.elim tail ktail a=v)]
    convert h.directed v using 1 <;> congr 1 <;> ext a <;> simp
  · intro v
    change Fintype.card {a:A // Sum.elim head khead a.val=v}=Fintype.card {s:S // s.val.1=v}
    rw [marked_finite_filter_card A (fun a=>Sum.elim head khead a=v),marked_finite_filter_card S (fun s=>s.1=v)]
    convert h.row v using 1 <;> congr 1 <;> ext a <;> simp
  · intro v
    change Fintype.card {a:A // Sum.elim head khead a.val=v∧markedArcType a.val=true}=
      Fintype.card {s:S // s.val.1=v∧decide (HK s.val.1 s.val.2)=true}
    simp only [decide_eq_true_eq]
    rw [marked_finite_filter_card A (fun a=>Sum.elim head khead a=v∧markedArcType a=true),marked_finite_filter_card S (fun s=>s.1=v∧HK s.1 s.2)]
    convert h.marked v using 1 <;> congr 1 <;> ext a <;> simp
  · intro u
    change Fintype.card {s:S // s.val.2=u∧decide (HK s.val.1 s.val.2)=false}=
      m*Fintype.card {s:S // s.val.2=u∧decide (HK s.val.1 s.val.2)=true}
    simp only [decide_eq_true_eq,decide_eq_false_iff_not]
    rw [marked_finite_filter_card S (fun s=>s.2=u∧¬HK s.1 s.2),marked_finite_filter_card S (fun s=>s.2=u∧HK s.1 s.2)]
    convert h.hub u using 1 <;> first | (congr 1; ext a; simp) | (congr 2; ext a; simp)


def markedRemainderRealization (tail head:E→V) (ktail khead:K→V)
    (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b:ℕ)
    (A:Finset (E⊕K)) (S:Finset (V×U))
    (hS:∀ s∈S,H₀ s.1 s.2∨HK s.1 s.2)
    (hsep:∀ a∈A,¬PermutationClose π b (Sum.elim tail ktail a) (Sum.elim head khead a))
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    IndexedMarkedHostRealization (markedRemainderGraph tail head ktail khead HK A S)
      tail head ktail khead H₀ HK π b where
  rows:=id
  hubs:=id
  rimPresent a:=by
    rcases a with ⟨a,ha⟩
    cases a with
    | inl a=>exact ⟨a,rfl,rfl⟩
    | inr a=>exact ⟨a,rfl,rfl⟩
  spokePresent s:=by
    change if decide (HK s.val.1 s.val.2) then HK s.val.1 s.val.2 else H₀ s.val.1 s.val.2
    by_cases h:HK s.val.1 s.val.2
    · simpa [h] using h
    · simpa [h] using (hS s.val s.property).resolve_right h
  arcSeparated a:=hsep a.val a.property
  rimInjective:=by
    intro a a' h
    apply Subtype.ext
    apply hp
    have he (a:A):
        (if (markedRemainderGraph tail head ktail khead HK A S).jr a then
          ({Sum.elim tail ktail a.val,π (Sum.elim head khead a.val)}:Finset V)
        else {Sum.elim tail ktail a.val,Sum.elim head khead a.val})=
        markedPhysicalEdge tail head ktail khead π a.val:=by
      rcases a with ⟨a,ha⟩
      cases a <;> rfl
    exact (he a).symm.trans (h.trans (he a'))
  spokeInjective:=by
    intro a a' h
    exact Subtype.ext h

theorem markedRemainderRealization_resources
    (tail head:E→V) (ktail khead:K→V)
    (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b:ℕ)
    (A:Finset (E⊕K)) (S:Finset (V×U))
    (hS:∀ s∈S,H₀ s.1 s.2∨HK s.1 s.2)
    (hsep:∀ a∈A,¬PermutationClose π b (Sum.elim tail ktail a) (Sum.elim head khead a))
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    (markedRemainderRealization tail head ktail khead H₀ HK π b A S hS hsep hp).resources=
      (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a)))∪S.image Sum.inr:=by
  ext e
  simp only [IndexedMarkedHostRealization.resources,markedRootGraphResources,
    Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro (⟨a,rfl⟩|⟨s,rfl⟩)
    · left
      refine ⟨a.val,a.property,?_⟩
      rcases a with ⟨a,ha⟩
      cases a <;> rfl
    · exact Or.inr ⟨s.val,s.property,rfl⟩
  · rintro (⟨a,ha,rfl⟩|⟨s,hs,rfl⟩)
    · left
      refine ⟨⟨a,ha⟩,?_⟩
      cases a <;> rfl
    · exact Or.inr ⟨⟨s,hs⟩,rfl⟩

end Oberwolfach
