module

public import Oberwolfach.OrdinaryBoundaryGraph
public import Oberwolfach.TriangleSupportEdges

@[expose] public section

/-! A complete physical graph on three rim vertices and one hub is an
ordinary three-wheel, with exactly the same six physical edge resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

def ordinaryWheelPhysicalGraph {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}
    (W:OrdinaryWheel Q F H r):SimpleGraph (V⊕U):=
  ordinaryPhysicalGraph (ordinaryWheelRim W)
    (fun v u=>u=ordinaryWheelHub W ∧ v∈(ordinaryWheelRim W).support)

theorem ordinaryWheelPhysicalGraph_edges {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}
    (W:OrdinaryWheel Q F H r):
    (ordinaryWheelPhysicalGraph W).edgeFinset=(ordinaryWheelResources W).image ordinaryPhysicalResource:=by
  ext e
  induction e using Sym2.ind with
  | _ x y=>
    cases x with
    | inl v=>
      cases y with
      | inl w=>
        simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,ordinaryWheelPhysicalGraph,ordinaryPhysicalGraph,
          Finset.mem_image]
        constructor
        · intro h;exact ⟨Sum.inl s(v,w),(ordinaryWheelResources_rim W _).mpr h,rfl⟩
        · rintro ⟨a,ha,he⟩
          have hid:ordinaryPhysicalResource a=ordinaryPhysicalResource (Sum.inl s(v,w)):=he
          have hh:=ordinaryPhysicalResource_injective hid
          subst a;exact (ordinaryWheelResources_rim W _).mp ha
      | inr u=>
        simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,ordinaryWheelPhysicalGraph,ordinaryPhysicalGraph,
          Finset.mem_image]
        constructor
        · intro h;exact ⟨Sum.inr (v,u),(ordinaryWheelResources_spoke W v u).mpr ⟨h.1.symm,h.2⟩,rfl⟩
        · rintro ⟨a,ha,he⟩
          have hid:ordinaryPhysicalResource a=ordinaryPhysicalResource (Sum.inr (v,u)):=he
          have hh:=ordinaryPhysicalResource_injective hid
          subst a
          have hs:=(ordinaryWheelResources_spoke W v u).mp ha
          exact ⟨hs.1.symm,hs.2⟩
    | inr u=>
      cases y with
      | inl v=>
        have he:s(Sum.inr u,Sum.inl v)=s(Sum.inl v,Sum.inr u):=Sym2.eq_swap
        rw [he]
        simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,ordinaryWheelPhysicalGraph,ordinaryPhysicalGraph,
          Finset.mem_image]
        constructor
        · intro h;exact ⟨Sum.inr (v,u),(ordinaryWheelResources_spoke W v u).mpr ⟨h.1.symm,h.2⟩,rfl⟩
        · rintro ⟨a,ha,he⟩
          have hid:ordinaryPhysicalResource a=ordinaryPhysicalResource (Sum.inr (v,u)):=he
          have hh:=ordinaryPhysicalResource_injective hid
          subst a
          have hs:=(ordinaryWheelResources_spoke W v u).mp ha
          exact ⟨hs.1.symm,hs.2⟩
      | inr z=>
        simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,ordinaryWheelPhysicalGraph,ordinaryPhysicalGraph,
          Finset.mem_image,false_iff,not_exists,not_and]
        intro a _ha he
        cases a with
        | inl a=>
          induction a using Sym2.ind with
          | _ v w=>
            change s(Sum.inl v,Sum.inl w)=s(Sum.inr u,Sum.inr z) at he
            rcases Sym2.eq_iff.mp he with ⟨h,_⟩|⟨h,_⟩ <;> exact Sum.inl_ne_inr h
        | inr a=>
          change s(Sum.inl a.1,Sum.inr a.2)=s(Sum.inr u,Sum.inr z) at he
          rcases Sym2.eq_iff.mp he with ⟨h,_⟩|⟨h,_⟩ <;> exact Sum.inl_ne_inr h

theorem ordinary_three_wheel_physical_complete {Q F:SimpleGraph V} {H:V→U→Prop}
    (W:OrdinaryWheel Q F H 3) (A:Finset V) (u:U)
    (hA:(ordinaryWheelRim W).support.toFinset=A) (hu:ordinaryWheelHub W=u):
    ordinaryWheelPhysicalGraph W=spanningRestriction ⊤ (A.image Sum.inl∪{Sum.inr u}):=by
  have htri:IsEmbeddedCycle (ordinaryWheelRim W) 3:=W.val.1.val.property
  have hmem (v:V):v∈(ordinaryWheelRim W).support↔v∈A:=by rw [←Set.mem_toFinset,hA]
  ext x y
  rw [spanningRestriction_adj]
  cases x <;> cases y <;>
    simp [ordinaryWheelPhysicalGraph,ordinaryPhysicalGraph,hu,htri.triangle_adj,hmem,
      SimpleGraph.top_adj,eq_comm,and_comm,and_left_comm,and_assoc]
  all_goals grind

theorem physical_triangle_wheel (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (u:U)
    (hA:A.card=3)
    (hclique:∀ x∈A.image Sum.inl∪{Sum.inr u},∀ y∈A.image Sum.inl∪{Sum.inr u},x≠y→
      (ordinaryPhysicalGraph Q H).Adj x y)
    (hF:∀ v∈A,∀ w∈A,¬F.Adj v w):
    ∃ W:OrdinaryWheel Q F H 3,
      (ordinaryWheelRim W).support.toFinset=A ∧ ordinaryWheelHub W=u ∧
      ordinaryWheelPhysicalGraph W=spanningRestriction ⊤ (A.image Sum.inl∪{Sum.inr u}):=by
  obtain ⟨x,y,z,hxy,hxz,hyz,hset⟩:=Finset.card_eq_three.mp hA
  have hx:x∈A:=by rw [hset];simp
  have hy:y∈A:=by rw [hset];simp
  have hz:z∈A:=by rw [hset];simp
  have hr (v w:V) (hv:v∈A) (hw:w∈A) (hne:v≠w):Q.Adj v w:=
    hclique (Sum.inl v) (by simp [hv]) (Sum.inl w) (by simp [hw]) (fun h=>hne (Sum.inl.inj h))
  obtain ⟨C,hC⟩:=triangle_cycle_from_vertices_support Q x y z hxy hxz hyz (hr x y hx hy hxy)
    (hr x z hx hz hxz) (hr y z hy hz hyz)
  have hc:C.val.val.support.toFinset=A:=hC.trans hset.symm
  have hh:∀ v∈C.val.val.support,H v u:=by
    intro v hv
    have hvA:v∈A:=by rw [←hc];exact Set.mem_toFinset.mpr hv
    exact hclique (Sum.inl v) (by simp [hvA]) (Sum.inr u) (by simp) (by simp)
  let W:OrdinaryWheel Q F H 3:=⟨(C,u),hh,by
    intro v hv w hw
    apply hF v _ w _
    · rw [←hc];exact Set.mem_toFinset.mpr hv
    · rw [←hc];exact Set.mem_toFinset.mpr hw⟩
  exact ⟨W,hc,rfl,ordinary_three_wheel_physical_complete W A u hc rfl⟩

end Oberwolfach
