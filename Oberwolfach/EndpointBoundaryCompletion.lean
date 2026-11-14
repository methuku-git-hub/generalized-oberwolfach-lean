module

public import Oberwolfach.BoundaryPairIncidences
public import Oberwolfach.IndexedBoundaryPaths

@[expose] public section

/-! Complete all selected endpoint assignments to ordinary wheels. The
reserved spokes and incidence bounds are derived from the assignments;
they are not additional extension or packing assumptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 6500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U J:Type} [Fintype V] [Fintype U] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq J]

theorem endpoint_boundary_completion (Q D₀ F:SimpleGraph V) (H E₀:V→U→Prop)
    (X:Finset V) (x:J↪V) (A:J→Finset V) (B:J→Finset U)
    (hx:∀ j,x j∉X) (hA:∀ j,A j⊆X)
    (hedge:∀ j,∀ a∈A j,Q.Adj (x j) a ∧ ¬D₀.Adj (x j) a ∧ ¬F.Adj (x j) a)
    (hroot:∀ j,∀ z∈B j,H (x j) z ∧ ¬E₀ (x j) z)
    (P:∀ j,EndpointPairing (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
      ((A j).image Sum.inl) ((B j).image Sum.inr))
    (hcross:∀ i j,i≠j→Disjoint (P i).graph (P j).graph)
    (hold:∀ j,Disjoint (P j).graph (ordinaryPhysicalGraph D₀ E₀))
    (r K D:ℕ) (hr:4≤r) (hK:0<K)
    (hsize:∀ j,(B j).card≤D)
    (hmemA:∀ a,(Finset.univ.filter (fun j=>a∈A j)).card≤D)
    (hmemB:∀ u,(Finset.univ.filter (fun j=>u∈B j)).card≤D)
    (L d₀ e₀ b:ℝ) (hL:0≤L) (hF:∀ a,(F.degree a:ℝ)≤L)
    (hD₀:∀ a∈X,(D₀.degree a:ℝ)≤d₀)
    (hE₀:∀ z,((Finset.univ.filter (fun a=>E₀ a z)).card:ℝ)≤e₀)
    (hcount:∀ j,∀ z∈B j,∀ a∈X,∀ c∈X,
      b≤(((X.filter (fun v=>H v z))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))
    (hbudget:(Fintype.card (Σ j,B j)*r:ℕ)/(K:ℝ)+((r:ℝ)+3)*(L+1)+
      2*(d₀+2*(K+D:ℕ))+e₀+(D*r:ℕ)+3*D<b):
    ∃ C:(Σ j,B j)→OrdinaryWheel Q F H r,
      (∀ i,ordinaryWheelHub (C i)=i.2.val ∧
        (∀ a∈(ordinaryWheelRim (C i)).support,a=x i.1∨a∈X) ∧
        Disjoint (ordinaryWheelResources (C i)) (ordinaryHostResources D₀ E₀)) ∧
      (∀ i j,i≠j→Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
      HasOrdinaryWheelDecomposition (wheelFamilyRim C) (wheelFamilySpokes C) r ∧
      (∀ a∉X,∀ v,(wheelFamilyRim C).Adj a v↔∃ j,a=x j ∧ v∈A j) ∧
      (∀ a∉X,∀ z,wheelFamilySpokes C a z↔∃ j,a=x j ∧ z∈B j) ∧
      (∀ a,(wheelFamilyRim C).degree a≤2*(K+D)) ∧
      (∀ a,(Finset.univ.filter (wheelFamilySpokes C a)).card≤K+D) ∧
      (∀ z,(Finset.univ.filter (fun a=>wheelFamilySpokes C a z)).card≤D*r):=by
  have hex (j:J):=typed_endpoint_pairing Q F H (A j) (B j) (P j)
  choose v w hvw using hex
  let I:Type:=Σ j,B j
  let xx:I→V:=fun i=>x i.1
  let vv:I→V:=fun i=>(v i.1 i.2).val
  let ww:I→V:=fun i=>(w i.1 i.2).val
  let uu:I→U:=fun i=>i.2.val
  have hselected (j:J) (z:B j):
      (P j).graph.Adj (Sum.inl (v j z).val) (Sum.inr z.val) ∧
      (P j).graph.Adj (Sum.inl (w j z).val) (Sum.inr z.val):=by
    rw [(hvw j).2.2.2.2]
    exact ⟨⟨z,rfl,Or.inl rfl⟩,⟨z,rfl,Or.inr rfl⟩⟩
  obtain ⟨hpairs,hspokes,hend,hhub⟩:=boundary_pair_incidences X x A B v w hx hA
    (fun j=>(hvw j).2.1) (fun j=>(P j).graph) hselected hcross D hsize hmemA hmemB
  let R:V→U→Prop:=fun a z=>∃ i:I,uu i=z ∧ a∈({xx i,vv i,ww i}:Finset V)
  have hR (z:U):((Finset.univ.filter (fun a=>R a z)).card:ℝ)≤3*D:=by
    have he:Finset.univ.filter (fun a=>R a z)=
        (Finset.univ.filter (fun i:I=>uu i=z)).biUnion (fun i=>({xx i,vv i,ww i}:Finset V)):=by
      ext a;simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion,R]
    have hh:(Finset.univ.filter (fun a=>R a z)).card≤3*D:=by
      rw [he]
      apply Finset.card_biUnion_le.trans
      calc
        _≤∑ _i∈Finset.univ.filter (fun i:I=>uu i=z),3:=
          Finset.sum_le_sum (fun _ _=>Finset.card_le_three)
        _=(Finset.univ.filter (fun i:I=>uu i=z)).card*3:=by simp
        _≤D*3:=Nat.mul_le_mul_right 3 (hhub z)
        _=3*D:=Nat.mul_comm _ _
    exact_mod_cast hh
  have hne (i:I):vv i≠ww i:=by
    intro he
    exact Set.disjoint_left.mp (hvw i.1).2.1 ⟨i.2,rfl⟩ ⟨i.2,Subtype.ext he.symm⟩
  have hfree (j:J) (z:B j):¬E₀ (v j z).val z.val ∧ ¬E₀ (w j z).val z.val:=by
    constructor
    · intro he
      exact disjoint_graphs_no_common_edge _ _ (hold j) _ _ (hselected j z).1 he
    · intro he
      exact disjoint_graphs_no_common_edge _ _ (hold j) _ _ (hselected j z).2 he
  have hroots (i:I) (a:V) (ha:a∈({xx i,vv i,ww i}:Finset V)):
      H a (uu i) ∧ ¬E₀ a (uu i) ∧ R a (uu i):=by
    refine ⟨?_,?_,i,rfl,ha⟩
    · rcases Finset.mem_insert.mp ha with h|h
      · rw [h];exact (hroot i.1 i.2.val i.2.property).1
      · rcases Finset.mem_insert.mp h with h|h
        · rw [h];exact ((hvw i.1).1 i.2).1
        · rw [Finset.mem_singleton.mp h];exact ((hvw i.1).1 i.2).2.1
    · rcases Finset.mem_insert.mp ha with h|h
      · rw [h];exact (hroot i.1 i.2.val i.2.property).2
      · rcases Finset.mem_insert.mp h with h|h
        · rw [h];exact (hfree i.1 i.2).1
        · rw [Finset.mem_singleton.mp h];exact (hfree i.1 i.2).2
  have hFroots (i:I):∀ a∈({xx i,vv i,ww i}:Finset V),∀ c∈({xx i,vv i,ww i}:Finset V),¬F.Adj a c:=by
    have h1:¬F.Adj (xx i) (vv i):=(hedge i.1 _ (v i.1 i.2).property).2.2
    have h2:¬F.Adj (xx i) (ww i):=(hedge i.1 _ (w i.1 i.2).property).2.2
    have h3:¬F.Adj (vv i) (ww i):=((hvw i.1).1 i.2).2.2
    intro a ha c hc
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hc
    rcases ha with rfl|rfl|rfl <;> rcases hc with rfl|rfl|rfl
    all_goals first | exact F.irrefl | exact h1 | exact h2 | exact h3 | exact fun h=>h1 h.symm | exact fun h=>h2 h.symm | exact fun h=>h3 h.symm
  obtain ⟨C,hC,hdis,_hcap,hrim,hrow,hcol⟩:=indexed_boundary_path_wheel_packing Q D₀ F H E₀ R X r K D hr hK
    xx vv ww uu (fun i=>hx i.1) (fun i=>hA i.1 (v i.1 i.2).property)
    (fun i=>hA i.1 (w i.1 i.2).property) hne
    (fun i=>(hedge i.1 _ (v i.1 i.2).property).1) (fun i=>(hedge i.1 _ (w i.1 i.2).property).1)
    (fun i=>(hedge i.1 _ (v i.1 i.2).property).2.1) (fun i=>(hedge i.1 _ (w i.1 i.2).property).2.1)
    hpairs hspokes hroots hFroots hend hhub L d₀ e₀ (3*D) b hL hF hD₀ hE₀
    (by intro z;convert hR z using 1;congr 2;ext a;simp only [Finset.mem_filter])
    (fun i=>hcount i.1 i.2.val i.2.property) hbudget
  have hboundary:=boundary_path_exact_edges C X xx vv ww uu hne
    (fun i=>(hC i).1) (fun i=>(hC i).2.1) (fun i=>(hC i).2.2.1) (fun i=>(hC i).2.2.2.1)
  refine ⟨C,fun i=>⟨(hC i).1,(hC i).2.2.2.1,(hC i).2.2.2.2.1⟩,
    hdis,wheelFamily_decomposition C hdis,?_,?_,hrim,hrow,hcol⟩
  · intro a ha b
    rw [hboundary.1 a ha b]
    constructor
    · rintro ⟨i,hi,hb|hb⟩
      · exact ⟨i.1,hi,hb ▸ (v i.1 i.2).property⟩
      · exact ⟨i.1,hi,hb ▸ (w i.1 i.2).property⟩
    · rintro ⟨j,hj,hb⟩
      rcases (hvw j).2.2.1 ⟨b,hb⟩ with ⟨z,hz⟩|⟨z,hz⟩
      · exact ⟨⟨j,z⟩,hj,Or.inl (congrArg Subtype.val hz).symm⟩
      · exact ⟨⟨j,z⟩,hj,Or.inr (congrArg Subtype.val hz).symm⟩
  · intro a ha z
    rw [hboundary.2 a ha z]
    constructor
    · rintro ⟨i,hi,hu⟩;exact ⟨i.1,hi,hu ▸ i.2.property⟩
    · rintro ⟨j,hj,hz⟩;exact ⟨⟨j,⟨z,hz⟩⟩,hj,rfl⟩

end Oberwolfach
