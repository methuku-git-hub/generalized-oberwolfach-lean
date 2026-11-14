module

public import Oberwolfach.MarkedSampleEndpointBalances
public import Oberwolfach.MarkedDeletedEndpointEmbeddings

@[expose] public section

/-! Actual finite remainder divisibility supplies the boundary selector's
three endpoint balances and its prescribed hub ratio. All classes use the
remaining graph; the spoke types are still those of the original host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Gamma Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Gamma] [Fintype Color]

theorem marked_remaining_boundary_row_balances_local
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Gamma Color)
    (H:Bool→V→U→Prop) (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (X:Finset V) (Z:Finset U) (v:V)
    (hH:∀ u,¬(H false v u∧H true v u)):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let src:=Sum.elim (fun e:E₀=>e.val.1) (fun e:E₁=>e.val.1)
    let dst:=Sum.elim (fun e:E₀=>e.val.2) (fun e:E₁=>e.val.2)
    let A:=Finset.univ.filter (fun a:E₀⊕E₁=>
      Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉DR.edgeFinset)
    let S:=Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧¬DS.Adj (Sum.inl z.1) (Sum.inr z.2));
    (A.filter (fun a=>dst a=v)).card=(A.filter (fun a=>src a=v)).card→
    (A.filter (fun a=>dst a=v)).card=(S.filter (fun s=>s.1=v)).card→
    (A.filter (fun a=>dst a=v∧markedArcType a=true)).card=(S.filter (fun s=>s.1=v∧H true s.1 s.2)).card→
    (∀ a∈A,dst a=v→src a∈X)→(∀ a∈A,src a=v→dst a∈X)→
    (∀ u,(v,u)∈S→u∈Z)→
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let A₀:=markedEndpointLabels P π d X (false,true,v) σ'
    let A₁:=markedEndpointLabels P π d X (true,true,v) σ'
    let X₀:=markedEndpointLabels P π d X (false,false,v) σ'
    let X₁:=markedEndpointLabels P π d X (true,false,v) σ'
    let Y₀:=Z.filter (H' false v)
    let Y₁:=Z.filter (H' true v);
    Disjoint Y₀ Y₁∧A₀.card+A₁.card=Y₀.card+Y₁.card∧
      X₀.card+X₁.card=Y₀.card+Y₁.card∧A₁.card=Y₁.card:=by
  intro E₀ E₁ src dst A S hdir hrow hmark hin hout hsp
  obtain ⟨hd,hr,hm⟩:=marked_sample_physical_deletion_local_row_balances P π d σ H DR DS v
    hdir hrow hmark
  apply marked_sample_endpoint_row_balances P π d (rawMarkedDeleteRims σ DR.edgeFinset)
    (markedDeletePhysicalSpokes H DS) X Z v
  · intro u hh
    exact hH u ⟨hh.1.1,hh.2.1⟩
  · intro u hu
    apply hsp u
    apply Finset.mem_filter.mpr
    rcases hu with h0|h1
    · exact ⟨Finset.mem_univ _,Or.inl h0.1,h0.2⟩
    · exact ⟨Finset.mem_univ _,Or.inr h1.1,h1.2⟩
  · intro a ha
    let f:=markedSampleDeletedArcsEmbedding P π d σ DR.edgeFinset
    have hf:f a∈A:=by
      have h:f a∈Finset.univ.image f:=Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
      rw [markedSampleDeletedArcsEmbedding_range] at h
      exact h
    have he:=markedSampleDeletedArcsEmbedding_endpoints_type P π d σ DR.edgeFinset a
    have hh:=hin (f a) hf (he.2.1.trans ha)
    exact he.1 ▸ hh
  · intro a ha
    let f:=markedSampleDeletedArcsEmbedding P π d σ DR.edgeFinset
    have hf:f a∈A:=by
      have h:f a∈Finset.univ.image f:=Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
      rw [markedSampleDeletedArcsEmbedding_range] at h
      exact h
    have he:=markedSampleDeletedArcsEmbedding_endpoints_type P π d σ DR.edgeFinset a
    have hh:=hout (f a) hf (he.1.trans ha)
    exact he.2.1 ▸ hh
  · exact hd
  · exact hr
  · exact hm

end Oberwolfach
