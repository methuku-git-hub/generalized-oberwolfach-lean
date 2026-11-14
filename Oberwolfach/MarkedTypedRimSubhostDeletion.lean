module

public import Oberwolfach.MarkedSampleOccurrenceMatrix
public import Oberwolfach.RawMarkedRimDeletion

@[expose] public section

/-! A typed physical rim subhost is obtained by deleting exactly its
missing physical edges. No equality of unused raw coordinates is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def markedRemovedPhysicalRim (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (e:Sym2 V):Prop:=
  ∃ mark x y,markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ∧
    markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y≠1 ∧
    e=s(x,if mark then π y else y)

theorem marked_typed_rim_subhost_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color)
    (hsub:∀ mark x y,markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 →
      markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1):
    ∃ D:SimpleGraph V,D≤P ∧
      (∀ x,D.degree x=(Finset.univ.filter (fun y=>x≠y ∧ markedRemovedPhysicalRim P π d σ τ s(x,y))).card) ∧
      ∀ mark x y,markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=
        markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ D.edgeFinset (Sum.inl e)) mark x y := by
  let Rem:=markedRemovedPhysicalRim P π d σ τ
  let D:SimpleGraph V:=SimpleGraph.fromEdgeSet {e | Rem e}
  letI hinst:Fintype D.edgeSet:=D.fintypeEdgeSet
  have hfin:@SimpleGraph.edgeFinset V D hinst=@SimpleGraph.edgeFinset V D D.fintypeEdgeSet:=by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
  have hmem (e:Sym2 V) (he:¬e.IsDiag):e∈D.edgeFinset↔Rem e:=by
    rw [SimpleGraph.mem_edgeFinset,SimpleGraph.edgeSet_fromEdgeSet]
    simp only [Set.mem_sdiff,Set.mem_ofPred_eq,Sym2.mem_diagSet,he,not_false_eq_true,and_true]
  have hadj (e:Sym2 V) (he:Rem e):e∈P.edgeSet:=by
    obtain ⟨mark,x,y,hσ,_,rfl⟩:=he
    exact ((markedPhysicalRim_eq_one_iff P π (3*d) (fun e=>σ (Sum.inl e)) mark x y).mp hσ).2.1
  refine ⟨D,?_,?_,?_⟩
  · intro x y h
    have hrem:Rem s(x,y):=((SimpleGraph.fromEdgeSet_adj _).mp h).1
    exact hadj _ hrem
  · intro x
    rw [←SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext y
    simp only [SimpleGraph.mem_neighborFinset,D,SimpleGraph.fromEdgeSet_adj,Set.mem_ofPred_eq,
      Finset.mem_filter,Finset.mem_univ,true_and,Rem]
    tauto
  · intro mark x y
    let e:Sym2 V:=s(x,if mark then π y else y)
    have hσ1 : markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 → ¬e.IsDiag:=by
      intro hh
      have hp:=((markedPhysicalRim_eq_one_iff P π (3*d) (fun e=>σ (Sum.inl e)) mark x y).mp hh).2.1
      dsimp [e];rw [Sym2.mk_isDiag_iff];exact hp.ne
    have hkeep : markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 → e∉D.edgeFinset:=by
      intro ht hd
      have hs:=hsub mark x y ht
      have hr:Rem e:=(hmem e (hσ1 hs)).mp hd
      obtain ⟨m',x',y',hs',ht',heq⟩:=hr
      have hu:=markedPhysicalRim_physical_unique P π (3*d) (fun e=>σ (Sum.inl e)) mark m' x y x' y' hs hs' heq
      obtain ⟨rfl,rfl,rfl⟩:=hu
      exact ht' ht
    have hlost : markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 →
        markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y≠1 → e∈D.edgeFinset:=by
      intro hs ht
      exact (hmem e (hσ1 hs)).mpr ⟨mark,x,y,hs,ht,rfl⟩
    have hiff : markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
        (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ∧ e∉D.edgeFinset):=by
      constructor
      · intro ht;exact ⟨hsub mark x y ht,hkeep ht⟩
      · rintro ⟨hs,he⟩
        by_contra ht
        exact he (hlost hs ht)
    have hdel : markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ D.edgeFinset (Sum.inl e)) mark x y=1 ↔
        (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ∧ e∉D.edgeFinset):=by
      cases mark with
      | false=>simpa [rawMarkedPairRims,markedPairPhysical,e] using rawMarkedDeleteRims_rims P π d σ D.edgeFinset (Sum.inl (x,y))
      | true=>simpa [rawMarkedPairRims,markedPairPhysical,e] using rawMarkedDeleteRims_rims P π d σ D.edgeFinset (Sum.inr (x,y))
    have hres:markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=
        markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ D.edgeFinset (Sum.inl e)) mark x y:=by
      rw [←markedPhysicalRim_indicator P π (3*d) (fun e=>τ (Sum.inl e)) mark x y,
        ←markedPhysicalRim_indicator P π (3*d) (fun e=>rawMarkedDeleteRims σ D.edgeFinset (Sum.inl e)) mark x y]
      have hh:=hiff.trans hdel.symm
      exact ite_congr (propext hh) (by intro _;rfl) (by intro _;rfl)
    convert hres using 1 <;> congr! 4 <;> ext e <;> simp [SimpleGraph.mem_edgeFinset]
end Oberwolfach
