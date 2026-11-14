module

public import Oberwolfach.MarkedCommonSubhostAgreement
public import Oberwolfach.MarkedFiniteRemainderTransfer

@[expose] public section
/-! Transfer actual terminal arcs from the modified host into the deleted
common host, with their type and both auxiliary endpoints unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_common_terminal_arc_agreement
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (DR:SimpleGraph V)
    (I X:Finset V) (hX:X⊆I) (hπ:∀ v,π v∈I↔v∈I)
    (hrim:∀ x y,x∈I→y∈I→σ (Sum.inl s(x,y))=τ (Sum.inl s(x,y)))
    (hcommon:∀ mark x y,x∈I→y∈I→
      markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x y=
      markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y):
    let E:=MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) true
    let E':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true
    let src:=Sum.elim (fun e:E=>e.val.1) (fun e:K=>e.val.1)
    let dst:=Sum.elim (fun e:E=>e.val.2) (fun e:K=>e.val.2)
    let src':=Sum.elim (fun e:E'=>e.val.1) (fun e:K'=>e.val.1)
    let dst':=Sum.elim (fun e:E'=>e.val.2) (fun e:K'=>e.val.2)
    let A₀:=Finset.univ.filter (fun a:E⊕K=>src a∈X∧dst a∈X);
    ∀ a:E'⊕K',src' a∈X→dst' a∈X→
      ∃ a₀∈A₀,src a₀=src' a∧dst a₀=dst' a∧markedArcType a₀=markedArcType a :=by
  intro E K E' K' src dst src' dst' A₀ a hx hy
  have hsame (mark:Bool) (x y:V) (hx:x∈X) (hy:y∈X):
      markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x y=
      markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y:=by
    rw [hcommon mark x y (hX hx) (hX hy)]
    have hy':(if mark then π y else y)∈I:=by cases mark <;> simp [hπ,hX hy]
    have hh:=hrim x (if mark then π y else y) (hX hx) hy'
    simp only [markedPhysicalRim,permutationSeparatedMatrix,markedPhysicalOrientation,hh]
  cases a with
  | inl e=>
    have ho:markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) false e.val.1 e.val.2=1:=by
      rw [hsame false e.val.1 e.val.2 hx hy];exact e.property
    let old:E:=⟨e.val,ho⟩
    refine ⟨Sum.inl old,?_,rfl,rfl,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx,hy⟩
  | inr e=>
    have ho:markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) true e.val.1 e.val.2=1:=by
      rw [hsame true e.val.1 e.val.2 hx hy];exact e.property
    let old:K:=⟨e.val,ho⟩
    refine ⟨Sum.inr old,?_,rfl,rfl,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx,hy⟩
end Oberwolfach
