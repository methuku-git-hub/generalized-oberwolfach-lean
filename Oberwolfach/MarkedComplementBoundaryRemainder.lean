module

public import Oberwolfach.MarkedPhysicalGraphLeftover
public import Oberwolfach.MarkedReservationComplement

@[expose] public section

/-! The boundary graph left by the complementary packing has degree
bounded by the actual unused physical resources of its restricted host.
Reserved boundary edges are excluded from this remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    [Fintype E] [Fintype K]

theorem marked_complement_boundary_remainder
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (H₀ HK:V→U→Prop)
    (m b:ℕ) (X:Finset V) (Z:Finset U) (hX:∀ x,π x∈X↔x∈X) (σ:Sym2 (V⊕U)→Bool):
    let PE:=fun e:E=>¬markedBoundaryRimAllowed π X σ false (tail e) (head e)
    let PK:=fun e:K=>¬markedBoundaryRimAllowed π X σ true (ktail e) (khead e)
    let t':=fun e:{e:E//PE e}=>tail e.val
    let h':=fun e:{e:E//PE e}=>head e.val
    let kt':=fun e:{e:K//PK e}=>ktail e.val
    let kh':=fun e:{e:K//PK e}=>khead e.val
    let H₀':=fun x u=>H₀ x u∧¬markedBoundarySpokeAllowed X Z σ x u
    let HK':=fun x u=>HK x u∧¬markedBoundarySpokeAllowed X Z σ x u;
    ∀ M:Finset (MarkedWheel t' h' kt' kh' m π b H₀' HK'),
    let Q:=physicalEdgeGraph (Finset.univ.image (markedPhysicalEdge tail head ktail khead π))
    let G:=ordinaryBoundaryGraph Q (fun x u=>H₀ x u∨HK x u) X Z
    let C:=ordinaryPhysicalGraph (markedPackingRimGraph M) (markedPackingSpokes M);
    Disjoint C (retainedGraph G σ)∧
    ∀ x,((G\retainedGraph G σ)\C).degree x≤
      (markedPhysicalIncidentEdges t' h' kt' kh' π H₀' HK' x\M.biUnion markedWheelPhysicalResources).card:=by
  intro PE PK t' h' kt' kh' H₀' HK' M Q G C
  have hex:=marked_reservation_complement_excludes m b X Z hX σ M
  have hC (x y:V⊕U) (hxy:C.Adj x y):
      markedPairResource x y∈M.biUnion markedWheelPhysicalResources:=by
    cases x with
    | inl x=>
      cases y with
      | inl y=>exact (markedPackingResources_rim M _).mpr hxy.2
      | inr u=>exact (markedPackingResources_spoke M x u).mpr hxy
    | inr u=>
      cases y with
      | inl x=>exact (markedPackingResources_spoke M x u).mpr hxy
      | inr v=>exact hxy.elim
  constructor
  · apply disjoint_iff_inf_le.mpr
    intro x y hxy
    obtain ⟨hc,hg⟩:=hxy
    have he:=hC x y hc
    obtain ⟨hg,hσ⟩:=hg
    rw [ordinaryBoundaryGraph_adj] at hg
    rcases x with x|u <;> rcases y with y|v
    · apply hex.1 false x y _ he
      apply Or.inr
      refine ⟨?_,hσ⟩
      simpa only [ordinaryInnerVertices_left] using hg.2.elim (fun h=>Or.inr h.2) (fun h=>Or.inl h.2)
    · apply hex.2 x v _ he
      apply Or.inr
      refine ⟨?_,hσ⟩
      simpa only [ordinaryInnerVertices_left,ordinaryInnerVertices_right] using hg.2.elim (fun h=>Or.inr h.2) (fun h=>Or.inl h.2)
    · apply hex.2 y u _ he
      apply Or.inr
      refine ⟨?_,?_⟩
      · simpa only [ordinaryInnerVertices_left,ordinaryInnerVertices_right] using hg.2.elim (fun h=>Or.inl h.2) (fun h=>Or.inr h.2)
      · simpa only [Sym2.eq_swap] using hσ
    · exact hg.1.elim
  · intro root
    have hU:∀ u v,¬((G\retainedGraph G σ)\C).Adj (Sum.inr u) (Sum.inr v):=by
      intro u v h
      exact ((ordinaryBoundaryGraph_adj Q _ X Z _ _).mp h.1.1).1
    have hS:∀ x y,((G\retainedGraph G σ)\C).Adj x y→
        markedPairResource x y∈Finset.univ.image (markedActivePhysical t' h' kt' kh' π H₀' HK')∧
        markedPairResource x y∉M.biUnion markedWheelPhysicalResources:=by
      intro x y h
      have hg:G.Adj x y:=h.1.1
      have hnσ:σ s(x,y)≠true:=fun hs=>h.1.2 ⟨hg,hs⟩
      have hnot:markedPairResource x y∉M.biUnion markedWheelPhysicalResources:=by
        intro he
        apply h.2
        rcases x with x|u <;> rcases y with y|v
        · exact ⟨(fun he=>hg.ne (congrArg Sum.inl he)), (markedPackingResources_rim M _).mp he⟩
        · exact (markedPackingResources_spoke M x v).mp he
        · exact (markedPackingResources_spoke M y u).mp he
        · exact ((ordinaryBoundaryGraph_adj Q _ X Z _ _).mp hg).1.elim
      refine ⟨?_,hnot⟩
      have hg':=(ordinaryBoundaryGraph_adj Q _ X Z _ _).mp hg
      have hrim (x y:V) (hq:Q.Adj x y)
          (hcross:(x∉X∧y∈X)∨(y∉X∧x∈X)) (hcoin:σ s(Sum.inl x,Sum.inl y)≠true):
          Sum.inl ({x,y}:Finset V)∈Finset.univ.image (markedActivePhysical t' h' kt' kh' π H₀' HK'):=by
        have hna:¬markedBoundaryRimAllowed π X σ false x y:=by
          simp only [markedBoundaryRimAllowed,Bool.false_eq_true,ite_false]
          tauto
        obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hq.2
        cases a with
        | inl e=>
          have he:PE e:=fun h=>hna ((marked_boundary_rim_allowed_physical_congr X hX σ false false
            (tail e) (head e) x y ha).mp h)
          exact Finset.mem_image.mpr ⟨Sum.inl (Sum.inl ⟨e,he⟩),Finset.mem_univ _,congrArg Sum.inl ha⟩
        | inr e=>
          have he:PK e:=fun h=>hna ((marked_boundary_rim_allowed_physical_congr X hX σ true false
            (ktail e) (khead e) x y ha).mp h)
          exact Finset.mem_image.mpr ⟨Sum.inl (Sum.inr ⟨e,he⟩),Finset.mem_univ _,congrArg Sum.inl ha⟩
      have hspoke (x:V) (u:U) (hh:H₀ x u∨HK x u)
          (hcross:(x∉X∧u∈Z)∨(u∉Z∧x∈X)) (hcoin:σ s(Sum.inl x,Sum.inr u)≠true):
          Sum.inr (x,u)∈Finset.univ.image (markedActivePhysical t' h' kt' kh' π H₀' HK'):=by
        have hna:¬markedBoundarySpokeAllowed X Z σ x u:=by
          simp only [markedBoundarySpokeAllowed]
          tauto
        have hh':H₀' x u∨HK' x u:=hh.imp (fun h=>⟨h,hna⟩) (fun h=>⟨h,hna⟩)
        exact Finset.mem_image.mpr ⟨Sum.inr ⟨(x,u),hh'⟩,Finset.mem_univ _,rfl⟩
      rcases x with x|u <;> rcases y with y|v
      · apply hrim x y hg'.1 _ hnσ
        simpa only [ordinaryInnerVertices_left] using hg'.2
      · apply hspoke x v hg'.1 _ hnσ
        simpa only [ordinaryInnerVertices_left,ordinaryInnerVertices_right] using hg'.2
      · apply hspoke y u hg'.1
        · simpa only [ordinaryInnerVertices_left,ordinaryInnerVertices_right,or_comm] using hg'.2
        · simpa only [Sym2.eq_swap] using hnσ
      · exact hg'.1.elim
    convert graph_degree_le_unused_marked_incident
      ((G\retainedGraph G σ)\C)
      (Finset.univ.image (markedActivePhysical t' h' kt' kh' π H₀' HK'))
      (M.biUnion markedWheelPhysicalResources) hU hS root using 1 <;> congr!
    unfold markedPhysicalIncidentEdges
    congr!
end Oberwolfach
