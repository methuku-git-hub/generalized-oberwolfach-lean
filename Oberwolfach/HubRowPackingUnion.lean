module

public import Oberwolfach.OrdinaryPackingGlue
public import Oberwolfach.RowCoverUnion

@[expose] public section

/-! The constructed hub wheels and subsequent row wheels together cover
all prescribed stars. Their physical edge sets and the actual deletion
remainder are retained; no new factor existence premise is introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r nh nr K:ℕ}

theorem relation_union_card_le {T:Type} [Fintype T] (A B:T→Prop):
    (Finset.univ.filter (fun x=>A x∨B x)).card≤
      (Finset.univ.filter A).card+(Finset.univ.filter B).card:=by
  have he:Finset.univ.filter (fun x=>A x∨B x)=Finset.univ.filter A∪Finset.univ.filter B:=by ext x;simp
  rw [he];exact Finset.card_union_le _ _

theorem ordinary_hub_row_union_packing_with_origins
    (M:Finset (OrdinaryWheel Q F H r))
    (u:Fin nh→U) (T:Fin nh→Finset V)
    (hunion:M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i))))
    (hT:∀ i,T i=Finset.univ.filter (fun v=>H v (u i)))
    (hM:∀ A∈M,∀ B∈M,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B))
    (hdegM:∀ v,(ordinaryWheelRimGraph M).degree v≤2*nh)
    (X:Finset V) (B:Finset U) (huB:∀ i,u i∉B)
    (C:Fin nr→Finset (OrdinaryWheel (Q\ordinaryWheelRimGraph M) F
      (fun v a=>H v a∧¬ordinaryPackingSpokes M v a) r))
    (x:Fin nr→V) (hxX:∀ i,x i∉X)
    (hc:∀ i,OrdinaryRowCover (C i) (x i) X K)
    (hcross:∀ i j,i≠j→Disjoint ((C i).biUnion ordinaryWheelResources) ((C j).biUnion ordinaryWheelResources)):
    ∃ P:Finset (OrdinaryWheel Q F H r),
      (∀ A∈P,∀ B∈P,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)) ∧
      P.biUnion ordinaryWheelResources=M.biUnion ordinaryWheelResources ∪
        (Finset.univ.biUnion C).biUnion ordinaryWheelResources ∧
      (∀ i a,(ordinaryWheelRimGraph P).Adj (x i) a↔Q.Adj (x i) a) ∧
      (∀ i a,ordinaryPackingSpokes P (x i) a↔H (x i) a) ∧
      (∀ i v,ordinaryPackingSpokes P v (u i)↔H v (u i)) ∧
      (∀ v∈X,(ordinaryWheelRimGraph P).degree v≤2*nh+nr*(2*(K+1))) ∧
      (∀ v∈X,(Finset.univ.filter (ordinaryPackingSpokes P v)).card≤nh+nr*(K+1)) ∧
      (∀ a∈B,(Finset.univ.filter (fun v=>ordinaryPackingSpokes P v a)).card≤nr*r) ∧
      (∀ W∈P,W∈M∨∃ Z∈Finset.univ.biUnion C,ordinaryWheelRim W=ordinaryWheelRim Z ∧ ordinaryWheelHub W=ordinaryWheelHub Z):=by
  let N:=Finset.univ.biUnion C
  have hn:=row_cover_union_packing C x X hc hcross
  have hd:=row_cover_union_degree_bounds C x X hxX hc
  obtain ⟨P,hP,hres,hrim,hsp,horigin⟩:=ordinary_wheel_packing_glue_with_origins M N hM hn.1
  refine ⟨P,hP,hres,?_,?_,?_,?_,?_,?_,horigin⟩
  · intro i a
    rw [hrim,SimpleGraph.sup_adj,hn.2.2.1]
    change (ordinaryWheelRimGraph M).Adj (x i) a∨
      (Q.Adj (x i) a∧¬(ordinaryWheelRimGraph M).Adj (x i) a)↔Q.Adj (x i) a
    have hsub:=ordinaryWheelRimGraph_subhost M (v:=x i) (w:=a)
    tauto
  · intro i a
    rw [hsp,hn.2.2.2]
    have hsub:ordinaryPackingSpokes M (x i) a→H (x i) a:=by
      rintro ⟨W,hW,hWu,hv⟩;rw [←hWu];exact W.property.1 (x i) hv
    tauto
  · intro i v
    constructor
    · rintro ⟨W,hW,hWu,hv⟩;rw [←hWu];exact W.property.1 v hv
    · intro hh
      apply (hsp v (u i)).mpr
      left
      apply (ordinary_hub_packing_spokes M u T hunion v (u i)).mpr
      exact ⟨i,rfl,by simpa only [hT,Finset.mem_filter,Finset.mem_univ,true_and] using hh⟩
  · intro v hv
    rw [hrim]
    convert (graph_sup_degree_le (ordinaryWheelRimGraph M) (ordinaryWheelRimGraph N) v).trans (Nat.add_le_add (hdegM v) (hd.1 v hv)) using 1 <;> congr!
  · intro v hv
    have he:Finset.univ.filter (ordinaryPackingSpokes P v)=
      Finset.univ.filter (fun a=>ordinaryPackingSpokes M v a∨ordinaryPackingSpokes N v a):=by ext a;simp only [Finset.mem_filter,hsp]
    rw [he]
    exact (relation_union_card_le _ _).trans (Nat.add_le_add (ordinary_hub_packing_row_degree M u T hunion v) (hd.2.1 v hv))
  · intro a ha
    have hno (v:V):¬ordinaryPackingSpokes M v a:=by
      intro hh
      obtain ⟨i,he,_⟩:=(ordinary_hub_packing_spokes M u T hunion v a).mp hh
      exact huB i (he ▸ ha)
    have he:Finset.univ.filter (fun v=>ordinaryPackingSpokes P v a)=
        Finset.univ.filter (fun v=>ordinaryPackingSpokes N v a):=by
      ext v;simp only [Finset.mem_filter,hsp,hno,false_or]
    rw [he];exact hd.2.2 a

theorem ordinary_hub_row_union_packing
    (M:Finset (OrdinaryWheel Q F H r))
    (u:Fin nh→U) (T:Fin nh→Finset V)
    (hunion:M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i))))
    (hT:∀ i,T i=Finset.univ.filter (fun v=>H v (u i)))
    (hM:∀ A∈M,∀ B∈M,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B))
    (hdegM:∀ v,(ordinaryWheelRimGraph M).degree v≤2*nh)
    (X:Finset V) (B:Finset U) (huB:∀ i,u i∉B)
    (C:Fin nr→Finset (OrdinaryWheel (Q\ordinaryWheelRimGraph M) F
      (fun v a=>H v a∧¬ordinaryPackingSpokes M v a) r))
    (x:Fin nr→V) (hxX:∀ i,x i∉X)
    (hc:∀ i,OrdinaryRowCover (C i) (x i) X K)
    (hcross:∀ i j,i≠j→Disjoint ((C i).biUnion ordinaryWheelResources) ((C j).biUnion ordinaryWheelResources)):
    ∃ P:Finset (OrdinaryWheel Q F H r),
      (∀ A∈P,∀ B∈P,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)) ∧
      P.biUnion ordinaryWheelResources=M.biUnion ordinaryWheelResources ∪
        (Finset.univ.biUnion C).biUnion ordinaryWheelResources ∧
      (∀ i a,(ordinaryWheelRimGraph P).Adj (x i) a↔Q.Adj (x i) a) ∧
      (∀ i a,ordinaryPackingSpokes P (x i) a↔H (x i) a) ∧
      (∀ i v,ordinaryPackingSpokes P v (u i)↔H v (u i)) ∧
      (∀ v∈X,(ordinaryWheelRimGraph P).degree v≤2*nh+nr*(2*(K+1))) ∧
      (∀ v∈X,(Finset.univ.filter (ordinaryPackingSpokes P v)).card≤nh+nr*(K+1)) ∧
      (∀ a∈B,(Finset.univ.filter (fun v=>ordinaryPackingSpokes P v a)).card≤nr*r):=by
  obtain ⟨P,hP,hres,hrow,hsp,hcol,hdeg,hrowdeg,hcoldeg,_⟩:=
    ordinary_hub_row_union_packing_with_origins M u T hunion hT hM hdegM X B huB C x hxX hc hcross
  exact ⟨P,hP,hres,hrow,hsp,hcol,hdeg,hrowdeg,hcoldeg⟩

end Oberwolfach
