module

public import Oberwolfach.OrdinaryActualRimVertexPacking
public import Oberwolfach.OrdinaryActualSpokeWheels

@[expose] public section

/-! The remaining cross-family checks involving spoke-edge wheels.
Fresh rim-edge hubs avoid all original and image spoke hubs. Rim-edge
collisions are ruled out using the actual disjoint path supports. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem rim_spoke_wheel_cross_disjoint {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}
    (E S:OrdinaryWheel Q F H r) (R P P':Finset V) (x:V) (hx:x∈R)
    (hPP:Disjoint P P') (hPR:Disjoint P R) (hP'R:Disjoint P' R)
    (hE:∀ v∈(ordinaryWheelRim E).support,v∈R∪P)
    (hS:∀ v∈(ordinaryWheelRim S).support,v=x∨v∈P')
    (hhub:ordinaryWheelHub E≠ordinaryWheelHub S):
    Disjoint (ordinaryWheelResources E) (ordinaryWheelResources S):=by
  apply transformer_wheel_pair_disjoint E S R P P' hPP hPR hP'R hE
  · intro v hv
    rcases hS v hv with he|hp
    · exact Finset.mem_union_left _ (he.symm ▸ hx)
    · exact Finset.mem_union_right _ hp
  · intro v hv w hw hadj
    have hvx:v=x:=by
      rcases hS v hadj.2.mem_support_left with h|h
      · exact h
      · exact (Finset.disjoint_left.mp hP'R h hv).elim
    have hwx:w=x:=by
      rcases hS w hadj.2.mem_support_right with h|h
      · exact h
      · exact (Finset.disjoint_left.mp hP'R h hw).elim
    exact hadj.2.ne (hvx.trans hwx.symm)
  · intro he;exact (hhub he).elim

 theorem ordinary_actual_spoke_cross_packing (G Q F:SimpleGraph V) (H₀ H:V→U→Prop)
    (φ:V→V) (ψ:U→U) (r:ℕ) (hr:3≤r) (R W:Finset V) (B:Finset U) (hRW:R⊆W)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v))
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)
    (hroot:∀ v∈G.support,v∈R∧φ v∈R)
    (hcross:∀ v∈G.support,∀ w∈G.support,φ v≠w)
    (hB:∀ e:{e:V×U // H₀ e.1 e.2},e.val.2∈B∧ψ e.val.2∈B)
    (hpW:∀ i,∀ v∈(p i).2.2.support,v∈W∧v∉R)
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)
    (E:OrdinaryActualRimWheels G Q F H₀ H φ r B b σ p)
    (S:OrdinaryActualSpokeWheels G Q F H₀ H φ ψ r p)
    (D:∀ d:Σ v,G.neighborSet v,
      OrdinaryVertexWheelPair Q F H r d.1 (φ d.1)
        (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)
        (transformerAssignedHub G σ E.hub d))
    (hD:∀ d,∀ v∈rootWheelInternal (D d).first d.1 (transformerRimEndpoint G Q H₀ p d)
        (transformerSpokeEndpoint G Q H₀ b p d),v∉W∧v≠φ d.1):
    (∀ e f,Disjoint (ordinaryWheelResources (E.first e)) (ordinaryWheelResources (S.first f)) ∧
      Disjoint (ordinaryWheelResources (E.second e)) (ordinaryWheelResources (S.second f))) ∧
    (∀ f d,Disjoint (ordinaryWheelResources (S.first f)) (ordinaryWheelResources (D d).second) ∧
      Disjoint (ordinaryWheelResources (S.second f)) (ordinaryWheelResources (D d).first)):=by
  have hfroot (f:{e:V×U // H₀ e.1 e.2}):f.val.1∈G.support:=balanced_spoke_root_mem_support G H₀ hbalance f
  have hP (i):Disjoint (p i).2.2.support.toFinset R:=
    Finset.disjoint_left.mpr (fun v hv=>(hpW i v (List.mem_toFinset.mp hv)).2)
  have heSupport (e:G.edgeFinset) (v:V) (hv:v∈(ordinaryWheelRim (E.first e)).support):
      v∈R∪(p (.inl e)).2.2.support.toFinset:=by
    have he:=edge_out_adj G e
    rcases (E.first_support e v).mp hv with rfl|rfl|hv
    · exact Finset.mem_union_left _ (hroot _ he.mem_support_left).1
    · exact Finset.mem_union_left _ (hroot _ he.mem_support_right).1
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr hv)
  have heSupport' (e:G.edgeFinset) (v:V) (hv:v∈(ordinaryWheelRim (E.second e)).support):
      v∈R∪(p (.inl e)).2.2.support.toFinset:=by
    have he:=edge_out_adj G e
    rcases (E.second_support e v).mp hv with rfl|rfl|hv
    · exact Finset.mem_union_left _ (hroot _ he.mem_support_left).2
    · exact Finset.mem_union_left _ (hroot _ he.mem_support_right).2
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr hv)
  constructor
  · intro e f
    have hPef:=hdis (.inl e) (.inr f) Sum.inl_ne_inr
    constructor
    · apply rim_spoke_wheel_cross_disjoint (E.first e) (S.first f) R _ _ f.val.1
        (hroot _ (hfroot f)).1 hPef (hP (.inl e)) (hP (.inr f)) (heSupport e)
      · intro v hv;simpa only [List.mem_toFinset] using (S.first_support f v).mp hv
      · rw [E.first_hub,S.first_hub]
        exact fun he=>E.hub_avoid e (he.symm ▸ (hB f).1)
    · apply rim_spoke_wheel_cross_disjoint (E.second e) (S.second f) R _ _ (φ f.val.1)
        (hroot _ (hfroot f)).2 hPef (hP (.inl e)) (hP (.inr f)) (heSupport' e)
      · intro v hv;simpa only [List.mem_toFinset] using (S.second_support f v).mp hv
      · rw [E.second_hub,S.second_hub]
        exact fun he=>E.hub_avoid e (he.symm ▸ (hB f).2)
  · intro f d
    have hd:G.Adj d.1 d.2.val:=d.2.property
    have hdf:=hd.mem_support_left
    have hu:transformerAssignedHub G σ E.hub d∉B:=E.hub_avoid _
    have hSW (v:V) (hv:v∈(ordinaryWheelRim (S.first f)).support):v∈W:=by
      rcases (S.first_support f v).mp hv with he|hp
      · exact hRW (he.symm ▸ (hroot _ (hfroot f)).1)
      · exact (hpW _ _ hp).1
    have hS'W (v:V) (hv:v∈(ordinaryWheelRim (S.second f)).support):v∈W:=by
      rcases (S.second_support f v).mp hv with he|hp
      · exact hRW (he.symm ▸ (hroot _ (hfroot f)).2)
      · exact (hpW _ _ hp).1
    have hnot:φ d.1∉(ordinaryWheelRim (S.first f)).support:=by
      intro hm
      rcases (S.first_support f _).mp hm with he|hp
      · exact hcross _ hdf _ (hfroot f) he
      · exact (hpW _ _ hp).2 (hroot _ hdf).2
    have hnot':d.1∉(ordinaryWheelRim (S.second f)).support:=by
      intro hm
      rcases (S.second_support f _).mp hm with he|hp
      · exact hcross _ (hfroot f) _ hdf he.symm
      · exact (hpW _ _ hp).2 (hroot _ hdf).1
    have hn (v:V):Sum.inr (v,ordinaryWheelHub (D d).second)∉ordinaryWheelResources (S.first f):=by
      intro hm
      have he:=((ordinaryWheelResources_spoke (S.first f) _ _).mp hm).1
      rw [S.first_hub,(D d).second_hub] at he
      exact hu (he ▸ (hB f).1)
    have hn' (v:V):Sum.inr (v,ordinaryWheelHub (D d).first)∉ordinaryWheelResources (S.second f):=by
      intro hm
      have he:=((ordinaryWheelResources_spoke (S.second f) _ _).mp hm).1
      rw [S.second_hub,(D d).first_hub] at he
      exact hu (he ▸ (hB f).2)
    have hanot (C:OrdinaryWheel Q F H r)
        (hsC:∀ v∈(ordinaryWheelRim C).support,v∈R∨v∈(p (.inr f)).2.2.support):
        transformerRimEndpoint G Q H₀ p d∉(ordinaryWheelRim C).support:=by
      intro hv
      have ha:=graphPathEndpoint_mem (p (.inl (rimIncidenceEquiv G d).1)) (rimIncidenceEquiv G d).2
      change transformerRimEndpoint G Q H₀ p d∈_ at ha
      rcases hsC _ hv with hR|hp
      · exact (hpW _ _ ha).2 hR
      · exact Finset.disjoint_left.mp (hdis (.inl (rimIncidenceEquiv G d).1) (.inr f) Sum.inl_ne_inr)
          (List.mem_toFinset.mpr ha) (List.mem_toFinset.mpr hp)
    have ha1:=hanot (S.first f) (fun v hv=>((S.first_support f v).mp hv).elim
      (fun he=>Or.inl (he.symm ▸ (hroot _ (hfroot f)).1)) Or.inr)
    have ha2:=hanot (S.second f) (fun v hv=>((S.second_support f v).mp hv).elim
      (fun he=>Or.inl (he.symm ▸ (hroot _ (hfroot f)).2)) Or.inr)
    constructor
    · apply edge_vertex_wheels_disjoint_without_attachment (S.first f) (D d).second (φ d.1) _ _
        (D d).second_a (D d).second_b (fun hadj=>ha1 hadj.mem_support_left) hnot _ (hn _) (hn _)
      intro v hv hw
      rw [vertex_pair_internal_second (D d) (fun v hv=>(hD d v hv).2)] at hv
      exact (hD d v hv).1 (hSW v hw)
    · apply edge_vertex_wheels_disjoint_without_attachment (S.second f) (D d).first d.1 _ _
        (D d).first_a (D d).first_b (fun hadj=>ha2 hadj.mem_support_left) hnot' _ (hn' _) (hn' _)
      intro v hv hw
      exact (hD d v hv).1 (hS'W v hw)

end Oberwolfach
