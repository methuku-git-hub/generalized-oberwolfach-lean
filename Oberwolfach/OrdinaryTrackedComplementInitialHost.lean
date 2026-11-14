module

public import Oberwolfach.OrdinaryTrackedComplementRootAgreement
public import Oberwolfach.OrdinaryComplementRemainderBalance
public import Oberwolfach.OrdinaryResourceRemovalExactBalance

@[expose] public section
/-! The actual remainder, after removing its same fixed absorber, satisfies
the host, balance and divisibility assumptions of the initial wheel step. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_complement_initial_host {n q r mAbs t aAbs bAbs:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (hS:S.IsRegularOfDegree (2*q)) (Inner Z Wterm A:Finset (Fin n)) (Hubs B Bterm:Finset (Fin q)) (ξ:ℝ)
    (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→Fin q→Prop)
    (cost:ℝ) (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n):
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (σ e)
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P raw\Bad
    let Href:=rawWheelSpokes π d raw false
    let Q:=S\ordinaryEmbeddedComplements Fs C f
    let H:=fun v u=>v∉Set.range (f u)
    let Gstart:=Q\ordinaryResourceRim Q K
    let Hstart:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    OrdinaryCorrectedProtectedReservoirWitness r mAbs t aAbs bAbs ξ Reference Bad Href
      A Z Wterm Bterm B K JQ JH→
    OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs K cost f→ Q≤P→
    Gstart≤P\Bad ∧
    (∀v,Gstart.degree v=2*(Finset.univ.filter (Hstart v)).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>Hstart v u)).card) ∧
    (∀w:Fin n⊕Fin q,((changed ((ordinaryPhysicalGraph Reference Href).neighborFinset w)
      ((ordinaryPhysicalGraph Gstart Hstart).neighborFinset w)).card:ℝ)≤cost) :=by
  intro raw Bad Reference Href Q H Gstart Hstart hw hf hQP
  have hfcopy:=hf
  unfold OrdinaryTrackedComplementFor at hfcopy
  obtain ⟨hC,hCC,hK,_,_,hBad,hphysical⟩:=hfcopy
  obtain ⟨hbal,hdiv⟩:=ordinary_complement_remainder_balance S hS Fs hFs C hsize f hC hCC
  have hb:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card:=by
    intro v
    convert hbal v using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  have hd:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card:=by
    intro u
    convert hdiv u using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  have hdec:=hw.2.2.2.2.2.1
  have hrem:=ordinary_resource_removal_exact_balance Q Reference Bad H Href r
    (by intro v;convert hb v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u;convert hd u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    K hK hdec
  refine ⟨?_,?_,?_,hphysical⟩
  · intro v w hvw
    have hQ:Q.Adj v w:=hvw.1
    exact ⟨hQP hQ,fun hbad=>(disjoint_iff_inf_le.mp hBad) ⟨hQ,hbad⟩⟩
  · intro v
    convert hrem.1 v using 1 <;> congr 8 <;> first | rfl | exact Subsingleton.elim _ _
  · intro u
    convert hrem.2 u using 1 <;> congr 8 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
