module

public import Oberwolfach.OrdinaryTriangleHubRowPacking

@[expose] public section
/-! If root-hub wheels avoid the inner rows, and root-row wheels use only
their designated root inside, the existing outside bounds hold everywhere
outside the designated root sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop}

theorem ordinary_hub_row_nonroot_support_bounds
    (nh nr:ℕ) (A:Finset V) (B:Finset U) (u:Fin nh→U) (x:Fin nr→V)
    (M:Finset (OrdinaryWheel Q F H 3))
    (hsupport:∀C∈M,(∃i,ordinaryWheelHub C=u i ∧ ∀v∈(ordinaryWheelRim C).support,v∈A) ∨
      (∃i,x i∈(ordinaryWheelRim C).support ∧ ordinaryWheelHub C∈B ∧
        ∀v∈(ordinaryWheelRim C).support,v=x i∨v∈A))
    (hR:∀v∈A,(ordinaryWheelRimGraph M).degree v≤2*nh+2*nr)
    (hS:∀v∈A,(Finset.univ.filter (ordinaryPackingSpokes M v)).card≤nh+nr)
    (hC:∀a∈B,(Finset.univ.filter (fun v=>ordinaryPackingSpokes M v a)).card≤3*nr):
    (∀v,(∀i,v≠x i)→(ordinaryWheelRimGraph M).degree v≤2*nh+2*nr) ∧
    (∀v,(∀i,v≠x i)→(Finset.univ.filter (ordinaryPackingSpokes M v)).card≤nh+nr) ∧
    (∀a,(∀i,a≠u i)→(Finset.univ.filter (fun v=>ordinaryPackingSpokes M v a)).card≤3*nr):=by
  have hnone:∀v, v∉A→(∀i,v≠x i)→∀C∈M,v∉(ordinaryWheelRim C).support:=by
    intro v hvA hvx C hC hv
    rcases hsupport C hC with ⟨i,_,hverts⟩|⟨i,_,_,hverts⟩
    · exact hvA (hverts v hv)
    · rcases hverts v hv with heq|ha
      · exact hvx i heq
      · exact hvA ha
  have hrimzero:∀v,(∀C∈M,v∉(ordinaryWheelRim C).support)→(ordinaryWheelRimGraph M).degree v=0:=by
    intro v hnone'
    rw [←SimpleGraph.card_neighborFinset_eq_degree,Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hadj:(ordinaryWheelRimGraph M).Adj v w:=(SimpleGraph.mem_neighborFinset _ _ _).mp hw
    obtain ⟨C,hC,hCedge⟩:=(ordinaryWheelRimGraph_edges M s(v,w)).mp hadj
    exact hnone' C hC ⟨w,hCedge⟩
  have hrowzero:∀v,(∀C∈M,v∉(ordinaryWheelRim C).support)→(Finset.univ.filter (ordinaryPackingSpokes M v)).card=0:=by
    intro v hnone'
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨C,hC,_,hv⟩:=(Finset.mem_filter.mp ha).2
    exact hnone' C hC hv
  have hcolzero:∀a,a∉B→(∀i,a≠u i)→(Finset.univ.filter (fun v=>ordinaryPackingSpokes M v a)).card=0:=by
    intro a haB hau
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨C,hC,hHub,_⟩:=(Finset.mem_filter.mp hv).2
    rcases hsupport C hC with ⟨i,hi,_⟩|⟨i,_,hi,_⟩
    · exact hau i (hHub.symm.trans hi)
    · exact haB (hHub ▸ hi)
  refine ⟨?_,?_,?_⟩
  · intro v hvx
    by_cases hvA:v∈A
    · exact hR v hvA
    · rw [hrimzero v (hnone v hvA hvx)]
      omega
  · intro v hvx
    by_cases hvA:v∈A
    · exact hS v hvA
    · rw [hrowzero v (hnone v hvA hvx)]
      omega
  · intro a hau
    by_cases haB:a∈B
    · exact hC a haB
    · rw [hcolzero a haB hau]
      omega
end Oberwolfach
