module

public import Oberwolfach.OrdinaryTrackedComplementWitness
public import Oberwolfach.OrdinaryComplementRemainderBalance

@[expose] public section
/-! The actual complement supplies the balance and local reference inputs
needed to run the two-host chain with the fixed absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_complement_two_host_inputs {n q r:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (hsizeC:∀u (c:↥(C u)),Fintype.card c.val=r)
    (hS:S.IsRegularOfDegree (2*q)) (Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (Wterm:Finset (Fin n)) (Bterm:Finset (Fin q)) (hW:Wterm⊆Inner) (hB:Bterm⊆Hubs)
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (editCost:ℝ)
    (hout:OrdinaryTrackedComplementOutcome P S π d σ Fs C Inner Hubs Kabs editCost):
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\Bad
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false;
    ∃f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n,
      OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs Kabs editCost f ∧
      let Q:=S\ordinaryEmbeddedComplements Fs C f
      let H:=fun v u=>v∉Set.range (f u);
      (∀v,Q.degree v=2*(Finset.univ.filter (H v)).card) ∧
      (∀u,r∣(Finset.univ.filter (fun v=>H v u)).card) ∧
      (∀v∈Wterm,∀w∈Wterm,Q.Adj v w→Reference.Adj v w) ∧
      (∀v∈Wterm,∀u∈Bterm,H v u→Href v u) :=by
  intro Bad Reference Href
  obtain ⟨f,hf⟩:=ordinary_tracked_complement_outcome_has_witness P S π d σ Fs C Inner Hubs Kabs editCost hout
  have hfcopy:=hf
  unfold OrdinaryTrackedComplementFor at hfcopy
  obtain ⟨hC,hCC,_,hpair,hspoke,_,_⟩:=hfcopy
  obtain ⟨hbal,hdiv⟩:=ordinary_complement_remainder_balance S hS Fs hFs C hsizeC f hC hCC
  refine ⟨f,hf,?_,?_,?_,?_⟩
  · intro v
    have hh:=hbal v
    convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  · intro u
    have hh:=hdiv u
    convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  · intro v hv w hw h
    exact (hpair v (hW hv) w (hW hw)).mp h
  · intro v hv u hu h
    exact (hspoke v (hW hv) u (hB hu)).mp h
end Oberwolfach
