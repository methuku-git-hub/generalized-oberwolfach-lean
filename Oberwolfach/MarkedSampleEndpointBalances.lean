module

public import Oberwolfach.MarkedEndpointArcExhaustion
public import Oberwolfach.MarkedHostRowData
public import Oberwolfach.MarkedSampleDeletionLocalBalances

@[expose] public section

/-! The endpoint classes in the boundary selector are the actual
neighbourhoods of the remaining sampled host. Their cardinal balances
follow from the corresponding finite incidence equalities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Gamma Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Gamma] [Fintype Color]

theorem marked_endpoint_labels_eq_neighbours
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (X:Finset V)
    (mark incoming:Bool) (x:V) (σ:RawMarkedOutcome V U Gamma Color)
    (hsupport:∀ e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) mark,
      (if incoming then e.val.2 else e.val.1)=x→(if incoming then e.val.1 else e.val.2)∈X):
    markedEndpointLabels P π d X (mark,incoming,x) σ=
      occurrenceRootNeighbours
        (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) mark=>if incoming then e.val.1 else e.val.2)
        (fun e=>if incoming then e.val.2 else e.val.1) x:=by
  ext y
  rw [marked_endpoint_labels_actual]
  simp only [Finset.mem_filter,occurrenceRootNeighbours,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hy,hp⟩
    refine ⟨⟨(if incoming then y else x,if incoming then x else y),hp⟩,?_,?_⟩ <;> cases incoming <;> rfl
  · rintro ⟨e,he,hr⟩
    refine ⟨he ▸ hsupport e hr,?_⟩
    have hp:(if incoming then y else x,if incoming then x else y)=e.val:=by
      cases incoming <;> apply Prod.ext <;> first | exact he.symm | exact hr.symm
    have hh:=congrArg (fun q:V×V=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark q.1 q.2) hp
    exact hh.trans e.property

theorem marked_sample_endpoint_row_balances
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Gamma Color)
    (H:Bool→V→U→Prop) (X:Finset V) (Z:Finset U) (v:V)
    (hH:∀ u,¬(H false v u∧H true v u))
    (hsp:∀ u,H false v u∨H true v u→u∈Z):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let src:=Sum.elim (fun e:E=>e.val.1) (fun e:K=>e.val.1)
    let dst:=Sum.elim (fun e:E=>e.val.2) (fun e:K=>e.val.2);
    (∀ a:E⊕K,dst a=v→src a∈X)→(∀ a:E⊕K,src a=v→dst a∈X)→
    (Finset.univ.filter (fun a:E⊕K=>dst a=v)).card=(Finset.univ.filter (fun a=>src a=v)).card→
    (Finset.univ.filter (fun a:E⊕K=>dst a=v)).card=
      (Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧z.1=v)).card→
    (Finset.univ.filter (fun a:E⊕K=>dst a=v∧markedArcType a=true)).card=
      (Finset.univ.filter (fun z:V×U=>H true z.1 z.2∧z.1=v)).card→
    let A₀:=markedEndpointLabels P π d X (false,true,v) σ
    let A₁:=markedEndpointLabels P π d X (true,true,v) σ
    let X₀:=markedEndpointLabels P π d X (false,false,v) σ
    let X₁:=markedEndpointLabels P π d X (true,false,v) σ
    let Y₀:=Z.filter (H false v)
    let Y₁:=Z.filter (H true v);
    Disjoint Y₀ Y₁∧A₀.card+A₁.card=Y₀.card+Y₁.card∧
      X₀.card+X₁.card=Y₀.card+Y₁.card∧A₁.card=Y₁.card:=by
  intro E K src dst hin hout hd hr hm A₀ A₁ X₀ X₁ Y₀ Y₁
  have hiE:Function.Injective (fun e:E=>(e.val.1,e.val.2)):=by
    intro e f he;exact Subtype.ext he
  have hiK:Function.Injective (fun e:K=>(e.val.1,e.val.2)):=by
    intro e f he;exact Subtype.ext he
  have hbal:=marked_neighbour_row_balances (fun e:E=>e.val.1) (fun e:E=>e.val.2)
    (fun e:K=>e.val.1) (fun e:K=>e.val.2) (H false) (H true) v hiE hiK hH hd hr hm
  have hA₀:A₀=occurrenceRootNeighbours (fun e:E=>e.val.1) (fun e:E=>e.val.2) v:=
    marked_endpoint_labels_eq_neighbours P π d X false true v σ (fun e he=>hin (Sum.inl e) he)
  have hA₁:A₁=occurrenceRootNeighbours (fun e:K=>e.val.1) (fun e:K=>e.val.2) v:=
    marked_endpoint_labels_eq_neighbours P π d X true true v σ (fun e he=>hin (Sum.inr e) he)
  have hX₀:X₀=occurrenceRootNeighbours (fun e:E=>e.val.2) (fun e:E=>e.val.1) v:=
    marked_endpoint_labels_eq_neighbours P π d X false false v σ (fun e he=>hout (Sum.inl e) he)
  have hX₁:X₁=occurrenceRootNeighbours (fun e:K=>e.val.2) (fun e:K=>e.val.1) v:=
    marked_endpoint_labels_eq_neighbours P π d X true false v σ (fun e he=>hout (Sum.inr e) he)
  have hY (b:Bool):Z.filter (H b v)=Finset.univ.filter (H b v):=by
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · exact And.right
    · intro hh
      refine ⟨hsp u ?_,hh⟩
      cases b
      · exact Or.inl hh
      · exact Or.inr hh
  dsimp only [Y₀,Y₁]
  rw [hA₀,hA₁,hX₀,hX₁,hY,hY]
  exact ⟨marked_actual_spoke_rows_disjoint (H false) (H true) v hH,hbal⟩

end Oberwolfach
