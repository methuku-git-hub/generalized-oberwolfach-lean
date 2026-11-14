module

public import Oberwolfach.OrdinaryPrescribedInnerNamed

@[expose] public section
/-! Instantiate the named event on the whole rim and hub domains, with the
actual protected sets chosen after sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_prescribed_family_from_event
    (P F Q:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
    (a p γ L:ℝ) (j:Color) (sample:RawWheelOutcome V U Γ Color)
    (hEvent:OrdinaryPrescribedInnerEvent 3 P F π d a p γ Finset.univ Finset.univ j sample)
    (hL:0≤L) (hLV:6*L≤(p^6*γ/4)*Fintype.card V)
    (hLU:6*L≤(p^6*γ/4)*Fintype.card U)
    (hQR:∀v,((changed ((rawWheelGraph P sample).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hHr:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d sample j v)) (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hHc:∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d sample j v u))
      (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L)
    (I:Finset V) (J:Finset U) (hI:(I.card:ℝ)≤p^6*γ*Fintype.card V/8)
    (hJ:(J.card:ℝ)≤p^6*γ*Fintype.card U/8)
    (Nr Ns D₀:ℕ) (v w:Fin Nr→V)
    (hv:∀i,v i∈I) (hw:∀i,w i∈I) (hvw:∀i,Q.Adj (v i) (w i)) (hFvw:∀i,¬F.Adj (v i) (w i))
    (hedge:∀i k,i≠k→¬((v i=v k∧w i=w k)∨(v i=w k∧w i=v k)))
    (hend:∀b,(Finset.univ.filter (fun i=>b=v i∨b=w i)).card≤D₀)
    (z:Fin Ns→V) (b:Fin Ns→U) (hz:∀i,z i∈I) (hb:∀i,b i∈J) (hH:∀i,H (z i) (b i))
    (hspoke:Function.Injective (fun i=>(z i,b i)))
    (hsend:∀t,(Finset.univ.filter (fun i=>t=z i)).card≤D₀)
    (hshub:∀t,(Finset.univ.filter (fun i=>b i=t)).card≤D₀)
    (hN:((Nr+Ns:ℕ):ℝ)≤a^2*(Fintype.card V:ℝ)^2) (hD₀:(D₀:ℝ)≤a*Fintype.card V):
    let e:(Fin Nr⊕Fin Ns)→Sym2 V⊕(V×U):=Sum.elim (fun i=>Sum.inl s(v i,w i)) (fun i=>Sum.inr (z i,b i));
    ∃ C:(Fin Nr⊕Fin Ns)→OrdinaryWheel Q F H 3,
      (∀i k,i≠k→Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C k))) ∧
      (∀i,ordinaryWheelResources (C i)∩ordinaryHostResources (spanningRestriction Q I)
        (fun t u=>H t u∧t∈I∧u∈J)={e i}) ∧
      (∀t,((wheelFamilyRim C).degree t:ℝ)≤12*a*Fintype.card V) ∧
      (∀t,((Finset.univ.filter (wheelFamilySpokes C t)).card:ℝ)≤6*a*Fintype.card V) ∧
      (∀u,((Finset.univ.filter (fun t=>wheelFamilySpokes C t u)).card:ℝ)≤9*a*Fintype.card V):=by
  dsimp only
  let X:=Finset.univ\I
  let B:=Finset.univ\J
  have hX:Finset.univ\X=I:=by ext t;simp [X]
  have hB:Finset.univ\B=J:=by ext t;simp [B]
  have h:=hEvent Q H L hL (by simpa only [Finset.card_univ] using hLV)
    (by simpa only [Finset.card_univ] using hLU)
    (by intro t;simpa only [Finset.univ_inter] using hQR t)
    (by intro t;simpa only [Finset.univ_inter] using hHr t)
    (by intro t _;simpa only [Finset.univ_inter] using hHc t)
    I X J B (by apply Finset.disjoint_left.mpr;intro t ht hh;exact (Finset.mem_sdiff.mp hh).2 ht)
    (by apply Finset.disjoint_left.mpr;intro t ht hh;exact (Finset.mem_sdiff.mp hh).2 ht)
    Nr Ns D₀ v w hv hw hvw hFvw hedge hend z b hz hb hH hspoke hsend hshub (Finset.subset_univ _)
    (by simpa only [Finset.card_univ] using hN) (by simpa only [Finset.card_univ] using hD₀)
    (by simpa only [hX,Finset.card_univ] using hI) (by simpa only [hB,Finset.card_univ] using hJ)
  obtain ⟨C,hC,hi,hd,hr,hc⟩:=h
  refine ⟨C,hC,hi,?_,?_,?_⟩
  · simpa only [Finset.card_univ] using hd
  · simpa only [Finset.card_univ] using hr
  · intro u;have hh:=hc u;simp only [Finset.card_univ] at hh; norm_num at hh; nlinarith only [hh]
end Oberwolfach
