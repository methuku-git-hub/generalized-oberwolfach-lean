module

public import Oberwolfach.HubRowPackingUnion

@[expose] public section

/-! The hub-and-row packing uses no other inner roots. Its individual
wheels retain the actual rim and hub of the original stage, rather than
being reconstructed from the union of their edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r nh nr K:ℕ}

theorem ordinary_hub_row_union_support (hr:0<r)
    (M:Finset (OrdinaryWheel Q F H r)) (u:Fin nh→U) (hu:Function.Injective u)
    (T:Fin nh→Finset V) (X:Finset V) (B:Finset U) (hTX:∀ i,T i⊆X)
    (hunion:M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i))))
    (C:Fin nr→Finset (OrdinaryWheel (Q\ordinaryWheelRimGraph M) F
      (fun v a=>H v a∧¬ordinaryPackingSpokes M v a) r)) (x:Fin nr→V)
    (hc:∀ i,OrdinaryRowCover (C i) (x i) X K)
    (hown:∀ i,∀ W∈C i,x i∈(ordinaryWheelRim W).support)
    (hB:∀ i a,H (x i) a→a∈B)
    (P:Finset (OrdinaryWheel Q F H r))
    (horigin:∀ W∈P,W∈M∨∃ Z∈Finset.univ.biUnion C,
      ordinaryWheelRim W=ordinaryWheelRim Z ∧ ordinaryWheelHub W=ordinaryWheelHub Z):
    ∀ W∈P,
      (∃ i,ordinaryWheelHub W=u i ∧ ∀ v∈(ordinaryWheelRim W).support,v∈X) ∨
      (∃ i,x i∈(ordinaryWheelRim W).support ∧ ordinaryWheelHub W∈B ∧
        ∀ v∈(ordinaryWheelRim W).support,v=x i∨v∈X):=by
  intro W hW
  rcases horigin W hW with hh|⟨Z,hZ,hR,hU⟩
  · obtain ⟨i,hi,hTi⟩:=ordinary_hub_packing_wheel_support M hr u hu T hunion W hh
    exact Or.inl ⟨i,hi,fun v hv=>hTX i (hTi v hv)⟩
  · obtain ⟨i,_,hZi⟩:=Finset.mem_biUnion.mp hZ
    have hroot:=hown i Z hZi
    refine Or.inr ⟨i,?_,?_,?_⟩
    · rw [hR];exact hroot
    · rw [hU];exact hB i _ (Z.property.1 (x i) hroot).1
    · rw [hR];exact (hc i).support Z hZi

theorem ordinary_packing_preserves_other_inner_stars
    (P:Finset (OrdinaryWheel Q F H r)) (I:Finset V) (J:Finset U)
    (u:Fin nh→U) (x:Fin nr→V)
    (hsupport:∀ W∈P,
      (∃ i,ordinaryWheelHub W=u i ∧ ∀ v∈(ordinaryWheelRim W).support,v∉I) ∨
      (∃ i,ordinaryWheelHub W∉J ∧ ∀ v∈(ordinaryWheelRim W).support,v=x i∨v∉I)):
    (∀ v∈I,(∀ i,v≠x i)→∀ w,¬(ordinaryWheelRimGraph P).Adj v w) ∧
    (∀ v∈I,(∀ i,v≠x i)→∀ a,¬ordinaryPackingSpokes P v a) ∧
    (∀ a∈J,(∀ i,a≠u i)→∀ v,¬ordinaryPackingSpokes P v a):=by
  have hno (v:V) (hv:v∈I) (hx:∀ i,v≠x i) (W:OrdinaryWheel Q F H r) (hW:W∈P):
      v∉(ordinaryWheelRim W).support:=by
    intro hh
    rcases hsupport W hW with ⟨i,hi,hs⟩|⟨i,hi,hs⟩
    · exact hs v hh hv
    · rcases hs v hh with he|he
      · exact hx i he
      · exact he hv
  refine ⟨?_,?_,?_⟩
  · intro v hv hx w hh
    obtain ⟨W,hW,he⟩:=(ordinaryWheelRimGraph_edges P s(v,w)).mp hh
    exact hno v hv hx W hW he.mem_support_left
  · intro v hv hx a hh
    obtain ⟨W,hW,_,he⟩:=hh
    exact hno v hv hx W hW he
  · intro a ha hu v hh
    obtain ⟨W,hW,hWa,hv⟩:=hh
    rcases hsupport W hW with ⟨i,hi,_⟩|⟨i,hi,_⟩
    · exact hu i (hWa.symm.trans hi)
    · exact hi (hWa.symm ▸ ha)

end Oberwolfach
