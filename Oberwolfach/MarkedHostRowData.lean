module

public import Oberwolfach.MarkedHostNeighbourEmbeddings
public import Oberwolfach.MarkedMatrixDivisibility
public import Oberwolfach.MarkedRowRequiredResources

@[expose] public section

/-! Row data are the actual neighbourhoods of the current host. The three
balances are needed only at the root, since deleting a reserved star need
not leave a globally divisible host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]

theorem marked_actual_spoke_rows_disjoint (H₀ HK:V→U→Prop) (v:V)
    (h:∀ u,¬(H₀ v u∧HK v u)):
    Disjoint (Finset.univ.filter (H₀ v)) (Finset.univ.filter (HK v)):=by
  apply Finset.disjoint_left.mpr
  intro u hu hk
  exact h u ⟨(Finset.mem_filter.mp hu).2,(Finset.mem_filter.mp hk).2⟩

theorem marked_neighbour_row_balances
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (v:V)
    (hinj₀:Function.Injective (fun e=>(tail e,head e)))
    (hinjₖ:Function.Injective (fun e=>(ktail e,khead e)))
    (hH:∀ u,¬(H₀ v u∧HK v u))
    (hdir:(Finset.univ.filter (fun a:E⊕K=>Sum.elim head khead a=v)).card=
      (Finset.univ.filter (fun a:E⊕K=>Sum.elim tail ktail a=v)).card)
    (hrow:(Finset.univ.filter (fun a:E⊕K=>Sum.elim head khead a=v)).card=
      (Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∨HK z.1 z.2)∧z.1=v)).card)
    (hmark:(Finset.univ.filter (fun a:E⊕K=>Sum.elim head khead a=v∧markedArcType a=true)).card=
      (Finset.univ.filter (fun z:V×U=>HK z.1 z.2∧z.1=v)).card):
    let A₀:=occurrenceRootNeighbours tail head v
    let A₁:=occurrenceRootNeighbours ktail khead v
    let X₀:=occurrenceRootNeighbours head tail v
    let X₁:=occurrenceRootNeighbours khead ktail v
    let Y₀:=Finset.univ.filter (H₀ v)
    let Y₁:=Finset.univ.filter (HK v)
    A₀.card+A₁.card=Y₀.card+Y₁.card∧
    X₀.card+X₁.card=Y₀.card+Y₁.card∧A₁.card=Y₁.card:=by
  have hi₀:Function.Injective (fun e=>(head e,tail e)):=by
    intro e f h;apply hinj₀;exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  have hiₖ:Function.Injective (fun e=>(khead e,ktail e)):=by
    intro e f h;apply hinjₖ;exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  dsimp only
  rw [occurrenceRootNeighbours_card tail head hinj₀,
    occurrenceRootNeighbours_card ktail khead hinjₖ,
    occurrenceRootNeighbours_card head tail hi₀,
    occurrenceRootNeighbours_card khead ktail hiₖ]
  have hsplit (f:E→V) (g:K→V):
      (Finset.univ.filter (fun a:E⊕K=>Sum.elim f g a=v)).card=
        (Finset.univ.filter (fun a:E=>f a=v)).card+(Finset.univ.filter (fun a:K=>g a=v)).card:=by
    simp only [Finset.card_filter,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  have htotal:(Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∨HK z.1 z.2)∧z.1=v)).card=
      (Finset.univ.filter (H₀ v)).card+(Finset.univ.filter (HK v)).card:=by
    have hrel:(Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∨HK z.1 z.2)∧z.1=v)).card=
        (Finset.univ.filter (fun u=>H₀ v u∨HK v u)).card:=by
      convert finite_relation_row_card (fun x u=>H₀ x u∨HK x u) v using 1 <;> congr!
    rw [hrel]
    have he:Finset.univ.filter (fun u=>H₀ v u∨HK v u)=
        (Finset.univ.filter (H₀ v))∪(Finset.univ.filter (HK v)):=by ext u;simp
    rw [he,Finset.card_union_of_disjoint (marked_actual_spoke_rows_disjoint H₀ HK v hH)]
  have hmarked:(Finset.univ.filter (fun a:E⊕K=>Sum.elim head khead a=v∧markedArcType a=true)).card=
      (Finset.univ.filter (fun a:K=>khead a=v)).card:=by
    simp only [Finset.card_filter,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,markedArcType,
      Bool.false_eq_true,and_false,ite_false,Finset.sum_const_zero,Bool.true_eq,and_true,zero_add]
  rw [hsplit,hsplit] at hdir
  rw [hsplit,htotal] at hrow
  rw [hmarked,finite_relation_row_card] at hmark
  exact ⟨hrow,hdir.symm.trans hrow,hmark⟩

theorem marked_neighbour_support_and_separation
    (f₀ g₀:E→V) (fₖ gₖ:K→V) (π:Equiv.Perm V) (b:ℕ) (v:V) (F:Finset V)
    (hsupport:∀ a:E⊕K,Sum.elim g₀ gₖ a=v→Sum.elim f₀ fₖ a∈F)
    (hsep:∀ a:E⊕K,Sum.elim g₀ gₖ a=v→
      ¬PermutationClose π b (Sum.elim f₀ fₖ a) v):
    occurrenceRootNeighbours f₀ g₀ v∪occurrenceRootNeighbours fₖ gₖ v⊆F∧
    ∀ x∈occurrenceRootNeighbours f₀ g₀ v∪occurrenceRootNeighbours fₖ gₖ v,
      ¬PermutationClose π b x v:=by
  have hh (x:V) (hx:x∈occurrenceRootNeighbours f₀ g₀ v∪occurrenceRootNeighbours fₖ gₖ v):
      ∃ a:E⊕K,Sum.elim f₀ fₖ a=x∧Sum.elim g₀ gₖ a=v:=by
    rcases Finset.mem_union.mp hx with hx|hx
    · obtain ⟨e,he,hg⟩:=(Finset.mem_filter.mp hx).2
      exact ⟨Sum.inl e,he,hg⟩
    · obtain ⟨e,he,hg⟩:=(Finset.mem_filter.mp hx).2
      exact ⟨Sum.inr e,he,hg⟩
  constructor
  · intro x hx;obtain ⟨a,rfl,ha⟩:=hh x hx;exact hsupport a ha
  · intro x hx;obtain ⟨a,rfl,ha⟩:=hh x hx;exact hsep a ha

end Oberwolfach
