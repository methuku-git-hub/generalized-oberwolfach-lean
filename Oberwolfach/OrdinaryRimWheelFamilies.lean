module

public import Oberwolfach.FreshTransformerHubs
public import Oberwolfach.TransformerWheelDisjointness

@[expose] public section

/-! Simultaneous rim-edge wheel pairs, with distinct actual hubs and
physical edge disjointness on both sides. Extra attachment labels are
included when choosing the hubs, after all paths have been selected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I]
  [DecidableEq V] [DecidableEq U] [DecidableEq I]

 theorem ordinary_rim_wheel_families (Q F:SimpleGraph V) (H:V→U→Prop)
    (r:ℕ) (hr:3≤r) (R:Finset V) (B:Finset U) (T:I→Finset V)
    (x y x' y':I→V) (p:I→(Σ a:V,Σ c:V,Q.Walk a c))
    (hroot:∀ i,x i∈R∧y i∈R∧x' i∈R∧y' i∈R)
    (hxy:∀ i,Q.Adj (x i) (y i)) (hxy':∀ i,Q.Adj (x' i) (y' i))
    (hcross:∀ i,x' i≠x i∧x' i≠y i∧y' i≠x i∧y' i≠y i)
    (hpath:∀ i,(p i).2.2.IsPath∧(p i).2.2.length=r-3)
    (hends:∀ i,Q.Adj (x i) (p i).1∧Q.Adj (x' i) (p i).1∧
      Q.Adj (y i) (p i).2.1∧Q.Adj (y' i) (p i).2.1)
    (havoid:∀ i,∀ v∈(p i).2.2.support,v∉R)
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)
    (hT:∀ i,(T i).card≤4)
    (hF:∀ i,∀ v∈({x i,y i,x' i,y' i}∪T i∪(p i).2.2.support.toFinset:Finset V),
      ∀ w∈({x i,y i,x' i,y' i}∪T i∪(p i).2.2.support.toFinset:Finset V),¬F.Adj v w)
    (hinj:Function.Injective (fun i=>s(x i,y i))) (hinj':Function.Injective (fun i=>s(x' i,y' i)))
    (b:ℝ) (hhubs:∀ S:Finset V,S.card≤r+6→(∀ v∈S,∀ w∈S,¬F.Adj v w)→
      b≤((common (Finset.univ:Finset U) S (fun v=>Finset.univ.filter (H v))).card:ℝ))
    (hbudget:B.card+Fintype.card I<b):
    ∃ (h:I↪U) (W W':I→OrdinaryWheel Q F H r),
      (∀ i,h i∉B∧(∀ v∈T i,H v (h i))) ∧
      (∀ i,ordinaryWheelHub (W i)=h i∧ordinaryWheelHub (W' i)=h i) ∧
      (∀ i,∀ v,v∈(ordinaryWheelRim (W i)).support↔v=x i∨v=y i∨v∈(p i).2.2.support) ∧
      (∀ i,∀ v,v∈(ordinaryWheelRim (W' i)).support↔v=x' i∨v=y' i∨v∈(p i).2.2.support) ∧
      (∀ i j,i≠j→Disjoint (ordinaryWheelResources (W i)) (ordinaryWheelResources (W j))) ∧
      (∀ i j,i≠j→Disjoint (ordinaryWheelResources (W' i)) (ordinaryWheelResources (W' j))) ∧
      (∀ i e,
        (if Sum.inl e∈ordinaryWheelResources (W i) then (1:ℤ) else 0)-
          (if Sum.inl e∈ordinaryWheelResources (W' i) then 1 else 0)=
        (if e=s(x i,y i) then 1 else 0)+(if e=s(x i,(p i).1) then 1 else 0)+
          (if e=s(y i,(p i).2.1) then 1 else 0)-(if e=s(x' i,y' i) then 1 else 0)-
          (if e=s(x' i,(p i).1) then 1 else 0)-(if e=s(y' i,(p i).2.1) then 1 else 0)) ∧
      (∀ i v z,
        (if Sum.inr (v,z)∈ordinaryWheelResources (W i) then (1:ℤ) else 0)-
          (if Sum.inr (v,z)∈ordinaryWheelResources (W' i) then 1 else 0)=
        (if v=x i∧z=h i then 1 else 0)+(if v=y i∧z=h i then 1 else 0)-
          (if v=x' i∧z=h i then 1 else 0)-(if v=y' i∧z=h i then 1 else 0)):=by
  let S:I→Finset V:=fun i=>{x i,y i,x' i,y' i}∪T i∪(p i).2.2.support.toFinset
  have hScard (i:I):(S i).card≤r+6:=by
    have hrootCard:({x i,y i,x' i,y' i}:Finset V).card≤4:=by
      have h1:=Finset.card_insert_le (x i) ({y i,x' i,y' i}:Finset V)
      have h2:=Finset.card_insert_le (y i) ({x' i,y' i}:Finset V)
      have h3:=Finset.card_insert_le (x' i) ({y' i}:Finset V)
      simp only [Finset.card_singleton] at h3
      omega
    have hpCard:(p i).2.2.support.toFinset.card≤r-2:=by
      have hh:=List.toFinset_card_le (p i).2.2.support
      rw [(p i).2.2.length_support,(hpath i).2] at hh
      omega
    have h1:=Finset.card_union_le ({x i,y i,x' i,y' i}:Finset V) (T i)
    have h2:=Finset.card_union_le (({x i,y i,x' i,y' i}:Finset V)∪T i) (p i).2.2.support.toFinset
    dsimp only [S];have ht:=hT i;omega
  obtain ⟨h,hB,hHS⟩:=fresh_transformer_hubs F H S B (r+6) b hScard hF hhubs hbudget
  have hw (i:I):∃ W W':OrdinaryWheel Q F H r,
      ordinaryWheelHub W=h i∧ordinaryWheelHub W'=h i∧
      (∀ v,v∈(ordinaryWheelRim W).support↔v=x i∨v=y i∨v∈(p i).2.2.support)∧
      (∀ v,v∈(ordinaryWheelRim W').support↔v=x' i∨v=y' i∨v∈(p i).2.2.support)∧
      (∀ e:Sym2 V,
        (if Sum.inl e∈ordinaryWheelResources W then (1:ℤ) else 0)-(if Sum.inl e∈ordinaryWheelResources W' then 1 else 0)=
        (if e=s(x i,y i) then 1 else 0)+(if e=s(x i,(p i).1) then 1 else 0)+
          (if e=s(y i,(p i).2.1) then 1 else 0)-(if e=s(x' i,y' i) then 1 else 0)-
          (if e=s(x' i,(p i).1) then 1 else 0)-(if e=s(y' i,(p i).2.1) then 1 else 0))∧
      (∀ v z,
        (if Sum.inr (v,z)∈ordinaryWheelResources W then (1:ℤ) else 0)-(if Sum.inr (v,z)∈ordinaryWheelResources W' then 1 else 0)=
        (if v=x i∧z=h i then 1 else 0)+(if v=y i∧z=h i then 1 else 0)-
          (if v=x' i∧z=h i then 1 else 0)-(if v=y' i∧z=h i then 1 else 0)):=by
    have hsmall:insert (x i) (insert (y i) (insert (x' i) (insert (y' i) (p i).2.2.support.toFinset)))⊆S i:=by
      intro v hv
      simp only [Finset.mem_insert] at hv
      rcases hv with hv|hv|hv|hv|hv
      · simp [S,hv]
      · simp [S,hv]
      · simp [S,hv]
      · simp [S,hv]
      · exact Finset.mem_union_right _ hv
    apply ordinary_edge_path_wheels Q F H r hr (x i) (y i) (x' i) (y' i) (p i).1 (p i).2.1 (h i)
      (p i).2.2 (hpath i).1 (hpath i).2 (hxy i) (hends i).1 (hends i).2.2.1
      (hxy' i) (hends i).2.1 (hends i).2.2.2
      (hcross i).1 (hcross i).2.1 (hcross i).2.2.1 (hcross i).2.2.2
    · intro v hv hvroot
      apply havoid i v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hvroot
      rcases hvroot with he|he|he|he
      · exact he.symm ▸ (hroot i).1
      · exact he.symm ▸ (hroot i).2.1
      · exact he.symm ▸ (hroot i).2.2.1
      · exact he.symm ▸ (hroot i).2.2.2
    · intro v hv w hw;exact hF i v (hsmall hv) w (hsmall hw)
    · intro v hv;exact hHS i v (hsmall hv)
  choose W W' hW using hw
  have hPR (i:I):Disjoint (p i).2.2.support.toFinset R:=by
    exact Finset.disjoint_left.mpr (fun v hv=>havoid i v (List.mem_toFinset.mp hv))
  refine ⟨h,W,W',?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i;exact ⟨hB i,fun v hv=>hHS i v (Finset.mem_union_left _ (Finset.mem_union_right _ hv))⟩
  · intro i;exact ⟨(hW i).1,(hW i).2.1⟩
  · intro i;exact (hW i).2.2.1
  · intro i;exact (hW i).2.2.2.1
  · intro i j hij
    apply two_root_rim_pair_disjoint (W i) (W j) R _ _ (x i) (y i) (x j) (y j)
      (hdis i j hij) (hPR i) (hPR j) (hroot i).1 (hroot i).2.1 (hroot j).1 (hroot j).2.1
    · intro v hv;simpa only [List.mem_toFinset] using ((hW i).2.2.1 v).mp hv
    · intro v hv;simpa only [List.mem_toFinset] using ((hW j).2.2.1 v).mp hv
    · exact fun he=>hij (hinj he)
    · rw [(hW i).1,(hW j).1];exact fun he=>hij (h.injective he)
  · intro i j hij
    apply two_root_rim_pair_disjoint (W' i) (W' j) R _ _ (x' i) (y' i) (x' j) (y' j)
      (hdis i j hij) (hPR i) (hPR j) (hroot i).2.2.1 (hroot i).2.2.2 (hroot j).2.2.1 (hroot j).2.2.2
    · intro v hv;simpa only [List.mem_toFinset] using ((hW i).2.2.2.1 v).mp hv
    · intro v hv;simpa only [List.mem_toFinset] using ((hW j).2.2.2.1 v).mp hv
    · exact fun he=>hij (hinj' he)
    · rw [(hW i).2.1,(hW j).2.1];exact fun he=>hij (h.injective he)
  · intro i;exact (hW i).2.2.2.2.1
  · intro i;exact (hW i).2.2.2.2.2

end Oberwolfach
