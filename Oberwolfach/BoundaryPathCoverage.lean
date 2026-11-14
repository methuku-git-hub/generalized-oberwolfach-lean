module

public import Oberwolfach.BoundaryPathPacking
public import Oberwolfach.OrdinaryPackingTransport
public import Oberwolfach.OrdinaryWheelFamilies

@[expose] public section

/-! Exact exterior incidences and physical degree bounds for boundary paths.
The prescribed triples are retained; no extra boundary edge is introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I]
  [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

theorem boundary_path_exact_edges (C:I→OrdinaryWheel Q F H r)
    (X:Finset V) (x v w:I→V) (u:I→U)
    (hvw:∀ i,v i≠w i) (hhub:∀ i,ordinaryWheelHub (C i)=u i)
    (hxv:∀ i,(ordinaryWheelRim (C i)).Adj (x i) (v i))
    (hxw:∀ i,(ordinaryWheelRim (C i)).Adj (x i) (w i))
    (hsupport:∀ i,∀ a∈(ordinaryWheelRim (C i)).support,a=x i∨a∈X):
    (∀ a∉X,∀ b,(wheelFamilyRim C).Adj a b↔∃ i,a=x i ∧ (b=v i∨b=w i)) ∧
    (∀ a∉X,∀ z,wheelFamilySpokes C a z↔∃ i,a=x i ∧ u i=z):=by
  constructor
  · intro a ha b
    rw [wheelFamilyRim,SimpleGraph.iSup_adj]
    constructor
    · rintro ⟨i,hi⟩
      have he:a=x i:=(hsupport i a hi.mem_support_left).resolve_right ha
      refine ⟨i,he,?_⟩
      have hb: b∈(ordinaryWheelRim (C i)).neighborFinset (x i):=
        ((ordinaryWheelRim (C i)).mem_neighborFinset _ _).mpr (he ▸ hi)
      rw [ordinaryWheel_root_neighbors (C i) (x i) (v i) (w i) (hvw i) (hxv i) (hxw i)] at hb
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hb
    · rintro ⟨i,rfl,hb|hb⟩
      · exact ⟨i,hb ▸ hxv i⟩
      · exact ⟨i,hb ▸ hxw i⟩
  · intro a ha z
    constructor
    · rintro ⟨i,hi,hia⟩
      exact ⟨i,(hsupport i a hia).resolve_right ha,(hhub i).symm.trans hi⟩
    · rintro ⟨i,rfl,hi⟩
      exact ⟨i,(hhub i).trans hi,(hxv i).mem_support_left⟩

theorem boundary_path_physical_degrees (C:I→OrdinaryWheel Q F H r) (K D:ℕ)
    (hrim:∀ v,(wheelFamilyRim C).degree v≤2*(K+D))
    (hrow:∀ v,(Finset.univ.filter (wheelFamilySpokes C v)).card≤K+D)
    (hcol:∀ u,(Finset.univ.filter (fun v=>wheelFamilySpokes C v u)).card≤D*r):
    (∀ v,(ordinaryPhysicalIncidentEdges (wheelFamilyRim C) (wheelFamilySpokes C) (Sum.inl v)).card≤3*(K+D)) ∧
    (∀ u,(ordinaryPhysicalIncidentEdges (wheelFamilyRim C) (wheelFamilySpokes C) (Sum.inr u)).card≤D*r):=by
  constructor
  · intro v
    rw [ordinaryPhysicalIncidentEdges_rim_card]
    exact (Nat.add_le_add (hrim v) (hrow v)).trans_eq (by omega)
  · intro u
    rw [ordinaryPhysicalIncidentEdges_hub_card]
    exact hcol u

theorem boundary_path_remainder_supported (C:I→OrdinaryWheel Q F H r)
    (X:Finset V) (J:Finset U) (x v w:I→V) (u:I→U)
    (hvw:∀ i,v i≠w i) (hhub:∀ i,ordinaryWheelHub (C i)=u i)
    (hxv:∀ i,(ordinaryWheelRim (C i)).Adj (x i) (v i))
    (hxw:∀ i,(ordinaryWheelRim (C i)).Adj (x i) (w i))
    (hsupport:∀ i,∀ a∈(ordinaryWheelRim (C i)).support,a=x i∨a∈X)
    (hQr:∀ a∉X,∀ b,Q.Adj a b→∃ i,a=x i ∧ (b=v i∨b=w i))
    (hHr:∀ a∉X,∀ z,H a z→∃ i,a=x i ∧ u i=z)
    (hHc:∀ z∉J,∀ a,¬H a z):
    (Q\wheelFamilyRim C).support⊆(X:Set V) ∧
      (∀ a z,H a z∧¬wheelFamilySpokes C a z→a∈X∧z∈J):=by
  have hex:=boundary_path_exact_edges C X x v w u hvw hhub hxv hxw hsupport
  constructor
  · intro a ha
    by_contra hn
    obtain ⟨b,hb⟩:=ha
    exact hb.2 ((hex.1 a hn b).mpr (hQr a hn b hb.1))
  · intro a z hz
    constructor
    · by_contra hn
      exact hz.2 ((hex.2 a hn z).mpr (hHr a hn z hz.1))
    · by_contra hn
      exact hHc z hn a hz.1

end Oberwolfach
