module

public import Oberwolfach.MarkedHostRowData
public import Oberwolfach.MarkedEndpointLabelIdentities

@[expose] public section

/-! The actual occurrence neighbourhoods of a sampled or deterministically
modified outcome coincide with its endpoint-label sets on the ambient domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sample_root_neighbours
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (mark incoming:Bool) (x:V):
    occurrenceRootNeighbours
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) mark=>if incoming then e.val.1 else e.val.2)
      (fun e=>if incoming then e.val.2 else e.val.1) x=
      markedEndpointLabels P π d Finset.univ (mark,incoming,x) σ:=by
  rw [marked_endpoint_labels_actual]
  ext z
  simp only [occurrenceRootNeighbours,Finset.mem_filter,Finset.mem_univ,true_and]
  cases incoming
  · simp only [Bool.false_eq_true,ite_false]
    constructor
    · rintro ⟨e,hz,hx⟩
      rw [←hz,←hx]
      exact e.property
    · intro hz
      exact ⟨⟨(x,z),hz⟩,rfl,rfl⟩
  · simp only [ite_true]
    constructor
    · rintro ⟨e,hz,hx⟩
      rw [←hz,←hx]
      exact e.property
    · intro hz
      exact ⟨⟨(z,x),hz⟩,rfl,rfl⟩

theorem marked_sample_row_cardinal_balances
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (x:V) (hH:∀ u,¬(H false x u∧H true x u))
    (hdir:
      (Finset.univ.filter (fun e:(MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false)⊕
        (MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true)=>
        Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) e=x)).card=
      (Finset.univ.filter (fun e:(MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false)⊕
        (MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true)=>
        Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) e=x)).card)
    (hrow:
      (Finset.univ.filter (fun e:(MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false)⊕
        (MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true)=>
        Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) e=x)).card=
      (Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧z.1=x)).card)
    (hmark:
      (Finset.univ.filter (fun e:(MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false)⊕
        (MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true)=>
        Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) e=x∧markedArcType e=true)).card=
      (Finset.univ.filter (fun z:V×U=>H true z.1 z.2∧z.1=x)).card):
    let A₀:=markedEndpointLabels P π d Finset.univ (false,true,x) σ
    let A₁:=markedEndpointLabels P π d Finset.univ (true,true,x) σ
    let X₀:=markedEndpointLabels P π d Finset.univ (false,false,x) σ
    let X₁:=markedEndpointLabels P π d Finset.univ (true,false,x) σ
    let Y₀:=Finset.univ.filter (H false x)
    let Y₁:=Finset.univ.filter (H true x)
    A₀.card+A₁.card=Y₀.card+Y₁.card ∧
    X₀.card+X₁.card=Y₀.card+Y₁.card ∧ A₁.card=Y₁.card:=by
  let f₀:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1
  let g₀:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.2
  let f₁:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1
  let g₁:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.2
  have h0:Function.Injective (fun e=>(f₀ e,g₀ e)):=by intro e f hef;exact Subtype.ext hef
  have h1:Function.Injective (fun e=>(f₁ e,g₁ e)):=by intro e f hef;exact Subtype.ext hef
  have hb:=marked_neighbour_row_balances f₀ g₀ f₁ g₁ (H false) (H true) x h0 h1 hH hdir hrow hmark
  dsimp only at hb ⊢
  have hin0:=marked_sample_root_neighbours P π d σ false true x
  have hin1:=marked_sample_root_neighbours P π d σ true true x
  have hout0:=marked_sample_root_neighbours P π d σ false false x
  have hout1:=marked_sample_root_neighbours P π d σ true false x
  change occurrenceRootNeighbours f₀ g₀ x=_ at hin0
  change occurrenceRootNeighbours f₁ g₁ x=_ at hin1
  change occurrenceRootNeighbours g₀ f₀ x=_ at hout0
  change occurrenceRootNeighbours g₁ f₁ x=_ at hout1
  rw [hin0,hin1,hout0,hout1] at hb
  exact hb

end Oberwolfach
