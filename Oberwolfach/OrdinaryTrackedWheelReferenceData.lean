module

public import Oberwolfach.OrdinaryTrackedComplementTwoHostInputsFor
public import Oberwolfach.OrdinaryCorrectedReservoirNamedWitness

@[expose] public section
/-! The actual tracked remainder and the fixed corrected reservoir supply
the balance, terminal agreement and absorber inputs for wheel cover-down. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTrackedWheelReferenceData {n q:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r mAbs:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q → SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (Wterm:Finset (Fin n)) (Bterm:Finset (Fin q))
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n):Prop :=
  let Bad:=permutationConflictGraph π (3*d)
  let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\Bad
  let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false
  let Q:=S\ordinaryEmbeddedComplements Fs C f
  let H:=fun v u=>v∉Set.range (f u);
  (∀v,Q.degree v=2*(Finset.univ.filter (H v)).card) ∧
  (∀u,r∣(Finset.univ.filter (fun v=>H v u)).card) ∧
  (∀v∈Wterm,∀w∈Wterm,Q.Adj v w → Reference.Adj v w) ∧
  (∀v∈Wterm,∀u∈Bterm,H v u → Href v u) ∧
  Kabs⊆ordinaryHostResources Q H ∧
  HasResourceDecomposition (ordinaryWheelResources (P:=Reference) (F:=Bad) (Hbase:=Href) (r:=r)) Kabs ∧
  ∀(G:SimpleGraph (Fin n)) (Hs:Fin n → Fin q → Prop),
    ordinaryHostResources G Hs⊆ordinaryRootResources Wterm Bterm → 
    (ordinaryPhysicalGraph G Hs).support.toFinset.card ≤ mAbs → 
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) → 
    (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card) → 
    G ≤ Reference → (∀v u,Hs v u → Href v u) → 
    IsResourceAbsorber (ordinaryWheelResources (P:=Reference) (F:=Bad) (Hbase:=Href) (r:=r))
      (ordinaryHostResources G Hs) Kabs

theorem ordinary_tracked_wheel_reference_data {n q r mAbs t aAbs bAbs:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q → SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent)
    (hsizeC:∀u (c:↥(C u)),Fintype.card c.val=r) (hS:S.IsRegularOfDegree (2*q))
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (A Z Wterm:Finset (Fin n)) (Bterm B:Finset (Fin q)) (ξ:ℝ)
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (JQ:SimpleGraph (Fin n)) (JH:Fin n → Fin q → Prop)
    (hWsub:Wterm⊆Inner) (hBsub:Bterm⊆Hubs) (editCost:ℝ)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n):
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\Bad
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false;
    OrdinaryCorrectedProtectedReservoirWitness r mAbs t aAbs bAbs ξ Reference Bad Href
      A Z Wterm Bterm B Kabs JQ JH → 
    OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs Kabs editCost f → 
    OrdinaryTrackedWheelReferenceData P S π d r mAbs σ Fs C Wterm Bterm Kabs f :=by
  intro Bad Reference Href hw hf
  obtain ⟨hbal,hdiv,hP,hH⟩:=ordinary_tracked_complement_two_host_inputs_for P S π d σ Fs hFs C hsizeC hS
    Inner Hubs Wterm Bterm hWsub hBsub Kabs editCost f hf
  have hfcopy:=hf
  unfold OrdinaryTrackedComplementFor at hfcopy
  obtain ⟨_,_,hA,_,_,_,_⟩:=hfcopy
  obtain ⟨_,_,_,_,_,hdec,hres,_,_,_,_,_,_,_,_⟩:=hw
  exact ⟨hbal,hdiv,hP,hH,hA,hdec,hres⟩
end Oberwolfach
