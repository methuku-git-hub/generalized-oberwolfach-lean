module

public import Oberwolfach.MarkedSparseInnerDomainPacking
public import Oberwolfach.MarkedPrescribedSubgraphPacking
public import Oberwolfach.MarkedBoundaryArcIndices
public import Oberwolfach.MarkedFiniteRemainder

@[expose] public section

/-! Pack a supplied finite set of inner typed arcs and spokes. The indexed
families used in the construction are enumerations of these very sets;
no new endpoints, edge multiplicities or incidence assumptions are added. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sparse_outside_subgraph_packing (l:ℕ) (hl:2≤l) (β:ℝ) (hβ:0<β)
    (η:ℝ) (hη:0<η) (hη1:η≤1) (hscale:100*((l:ℝ)+20)*η≤β):
    ∀ b:ℕ,1≤b→∃ n₀:ℕ,
    ∀ (V U E K:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    ∀ (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V),n₀≤Fintype.card V→
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→
    ∀ (X:Finset V) (Z:Finset U),(∀ v,π v∈X↔v∈X)→
    (∀ u,∀ t x,β*Fintype.card V≤((X.filter (fun z=>markedArcPresent tail head ktail khead t x z∧
      (if t then HK z u else H₀ z u))).card:ℝ))→
    (∀ u,∀ t x y,x≠(if t then π y else y)→β*Fintype.card V≤((X.filter (fun z=>
      markedArcPresent tail head ktail khead false x z∧
      markedArcPresent tail head ktail khead t z y∧H₀ z u)).card:ℝ))→
    ∀ (A:Finset (E⊕K)) (S:Finset (V×U)),
    (A.card:ℝ)≤η^2*(Fintype.card V:ℝ)^2→(S.card:ℝ)≤η^2*(Fintype.card V:ℝ)^2→
    (∀ a∈A,Sum.elim tail ktail a∉X∧Sum.elim head khead a∉X)→
    (∀ a∈A,¬PermutationClose π b (Sum.elim tail ktail a) (Sum.elim head khead a))→
    (∀ v,((A.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤η^2*Fintype.card V)→
    (∀ a∈A,β*Fintype.card V≤((Z.filter (fun u=>H₀ (Sum.elim tail ktail a) u∧
      (if markedArcType a then HK (Sum.elim head khead a) u else H₀ (Sum.elim head khead a) u))).card:ℝ))→
    (∀ z∈S,z.1∉X∧z.2∉Z∧(H₀ z.1 z.2∨HK z.1 z.2))→
    (∀ v,((S.filter (fun z=>v=z.1)).card:ℝ)≤η^2*Fintype.card V)→
    (∀ u,((S.filter (fun z=>z.2=u)).card:ℝ)≤η^2*Fintype.card V)→
    ∃ M:Finset (MarkedWheel tail head ktail khead (l+4) π b H₀ HK),
      (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource (Xᶜ) (Zᶜ))=
        A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr∧
      (∀ v,((markedPackingRimGraph M).degree v:ℝ)≤24*η*Fintype.card V)∧
      (∀ v,((Finset.univ.filter (markedPackingSpokes M v)).card:ℝ)≤6*η*Fintype.card V)∧
      (∀ u,((Finset.univ.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤3*(l+5)*η*Fintype.card V):=by
  intro b hb
  obtain ⟨n₀,hbase⟩:=marked_sparse_inner_domain_packing l hl β hβ η hη hη1 hscale b hb
  refine ⟨n₀,?_⟩
  intro V U E K _ _ _ _ tail head ktail khead H₀ HK π hn hp X Z hX hstep hjoin A S hAcard hScard hArows hAsep hAdeg hhubs hS hSrow hScol
  let eA:Fin A.card≃A:=(Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm
  let eS:Fin S.card≃S:=(Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
  let a:Fin A.card→E⊕K:=fun i=>(eA i).val
  let x:=fun i=>Sum.elim tail ktail (a i)
  let y:=fun i=>Sum.elim head khead (a i)
  let tr:=fun i=>markedArcType (a i)
  let z:=fun i=>(eS i).val.1
  let u:=fun i=>(eS i).val.2
  let ts:=fun i=>decide (HK (z i) (u i))
  have hphys (i:Fin A.card):(if tr i then ({x i,π (y i)}:Finset V) else {x i,y i})=
      markedPhysicalEdge tail head ktail khead π (a i):=by
    have he (a':E⊕K):(if markedArcType a' then
        ({Sum.elim tail ktail a',π (Sum.elim head khead a')}:Finset V)
        else {Sum.elim tail ktail a',Sum.elim head khead a'})=
        markedPhysicalEdge tail head ktail khead π a':=by cases a' <;> rfl
    exact he (a i)
  have hpres (i:Fin A.card):markedArcPresent tail head ktail khead (tr i) (x i) (y i):=by
    dsimp only [tr,x,y]
    cases a i with
    | inl a=>exact ⟨a,rfl,rfl⟩
    | inr a=>exact ⟨a,rfl,rfl⟩
  have hinj:Function.Injective (fun i=>if tr i then ({x i,π (y i)}:Finset V) else {x i,y i}):=by
    intro i j h
    apply eA.injective
    apply Subtype.ext
    apply hp
    rw [←hphys,←hphys]
    exact h
  have hdeg (v:V):((Finset.univ.filter (fun i=>v=x i∨v=y i)).card:ℝ)≤η^2*Fintype.card V:=by
    have he:(Finset.univ.filter (fun i=>v=x i∨v=y i)).card=
        (A.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:=by
      convert finite_enumeration_filter_card A eA (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a) using 1 <;> congr!
    rw [he];exact hAdeg v
  have hsrow (v:V):((Finset.univ.filter (fun i=>v=z i)).card:ℝ)≤η^2*Fintype.card V:=by
    have he:(Finset.univ.filter (fun i=>v=z i)).card=(S.filter (fun z=>v=z.1)).card:=by
      convert finite_enumeration_filter_card S eS (fun z=>v=z.1) using 1 <;> congr!
    rw [he];exact hSrow v
  have hscol (w:U):((Finset.univ.filter (fun i=>u i=w)).card:ℝ)≤η^2*Fintype.card V:=by
    have he:(Finset.univ.filter (fun i=>u i=w)).card=(S.filter (fun z=>z.2=w)).card:=by
      convert finite_enumeration_filter_card S eS (fun z=>z.2=w) using 1 <;> congr!
    rw [he];exact hScol w
  have hsp (i:Fin S.card):if ts i then HK (z i) (u i) else H₀ (z i) (u i):=by
    have hs:=(hS (eS i).val (eS i).property).2.2
    dsimp only [ts]
    split_ifs with hk
    · exact of_decide_eq_true hk
    · have hn:¬HK (z i) (u i):=of_decide_eq_false (Bool.eq_false_iff.mpr hk)
      exact hs.resolve_right hn
  have hsinj:Function.Injective (fun i=>(z i,u i)):=by
    intro i j h
    apply eS.injective
    exact Subtype.ext h
  obtain ⟨M,hM,hinner,hr,hs,hc⟩:=hbase V U E K tail head ktail khead H₀ HK π hn hp X Z hX hstep hjoin
    A.card S.card hAcard hScard x y tr
    (fun i=>(hArows (a i) (eA i).property).1) (fun i=>(hArows (a i) (eA i).property).2)
    (fun i=>hAsep (a i) (eA i).property) hpres hinj hdeg (fun i=>hhubs (a i) (eA i).property) z u ts
    (fun i=>(hS (eS i).val (eS i).property).1) (fun i=>(hS (eS i).val (eS i).property).2.1)
    hsp hsinj hsrow hscol
  refine ⟨M,hM,?_,hr,hs,hc⟩
  rw [hinner]
  congr 1
  · ext r
    simp only [Finset.mem_image,Finset.mem_univ,true_and,hphys]
    constructor
    · rintro ⟨i,he⟩;exact ⟨a i,(eA i).property,he⟩
    · rintro ⟨a',ha,he⟩
      obtain ⟨i,hi⟩:=eA.surjective ⟨a',ha⟩
      exact ⟨i,by simpa only [a,hi] using he⟩
  · ext r
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,he⟩;exact ⟨(eS i).val,(eS i).property,he⟩
    · rintro ⟨z',hz,he⟩
      obtain ⟨i,hi⟩:=eS.surjective ⟨z',hz⟩
      exact ⟨i,by simpa only [z,u,hi] using he⟩

end Oberwolfach
