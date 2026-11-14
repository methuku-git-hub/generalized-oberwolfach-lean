module

public import Oberwolfach.OrdinaryPairedRootWheels
public import Oberwolfach.FiniteDisjointChoices

@[expose] public section

/-! A vertex-wheel pair retains its actual two cycles, prescribed root
edges and signed physical differences. The simultaneous constructor
chooses fresh internal vertices for all such pairs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I]
  [DecidableEq V] [DecidableEq U] [DecidableEq I]

 structure OrdinaryVertexWheelPair (Q F:SimpleGraph V) (H:V→U→Prop)
    (r:ℕ) (x y a b:V) (u:U) where
  first : OrdinaryWheel Q F H r
  second : OrdinaryWheel Q F H r
  first_hub : ordinaryWheelHub first=u
  second_hub : ordinaryWheelHub second=u
  first_a : (ordinaryWheelRim first).Adj x a
  first_b : (ordinaryWheelRim first).Adj x b
  second_a : (ordinaryWheelRim second).Adj y a
  second_b : (ordinaryWheelRim second).Adj y b
  second_rim : ordinaryWheelRim second=(ordinaryWheelRim first).map (Equiv.swap x y).toEmbedding
  second_support : ∀ v,v∈(ordinaryWheelRim second).support↔v=y∨(v∈(ordinaryWheelRim first).support∧v≠x)
  rim_difference : ∀ e:Sym2 V,
    (if Sum.inl e∈ordinaryWheelResources first then (1:ℤ) else 0)-
      (if Sum.inl e∈ordinaryWheelResources second then 1 else 0)=
    (if e∈({s(x,a),s(x,b)}:Finset (Sym2 V)) then 1 else 0)-
      (if e∈({s(y,a),s(y,b)}:Finset (Sym2 V)) then 1 else 0)
  spoke_difference : ∀ v z,
    (if Sum.inr (v,z)∈ordinaryWheelResources first then (1:ℤ) else 0)-
      (if Sum.inr (v,z)∈ordinaryWheelResources second then 1 else 0)=
    (if v=x∧z=u then 1 else 0)-(if v=y∧z=u then 1 else 0)

 theorem ordinary_vertex_wheel_pair (Q F:SimpleGraph V) (H:V→U→Prop)
    (A W Ω:Finset V) (hAΩ:A⊆Ω) (x y a b:V) (u:U)
    (hxy:x≠y) (hab:a≠b) (haΩ:a∈Ω) (hbΩ:b∈Ω)
    (hxa:Q.Adj x a) (hxb:Q.Adj x b) (hya:Q.Adj y a) (hyb:Q.Adj y b)
    (hFroot:∀ v∈({x,a,b}:Finset V),∀ w∈({x,a,b}:Finset V),¬F.Adj v w)
    (hFy:¬F.Adj y a∧¬F.Adj y b) (hH:H x u∧H y u∧H a u∧H b u)
    (hHA:∀ v∈A,H v u) (r:ℕ) (hr:4≤r) (L t:ℝ) (hL:0≤L) (hF:∀ v,(F.degree v:ℝ)≤L)
    (hcount:∀ v∈Ω,∀ w∈Ω,t≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hbudget:W.card+((r:ℝ)+4)*(L+1)<t):
    ∃ D:OrdinaryVertexWheelPair Q F H r x y a b u,
      ∀ v∈rootWheelInternal D.first x a b,v∈A∧v∉W∧v≠y:=by
  obtain ⟨C,C',hCu,hC'u,hCxa,hCxb,hC'ya,hC'yb,hmap,hclass,hsupport,hrim,hspoke⟩:=
    ordinary_paired_root_wheels Q F H A W Ω hAΩ x y a b u u hxy hab haΩ hbΩ
      hxa hxb hya hyb hFroot hFy ⟨hH.1,hH.2.1,hH.2.2.1,hH.2.2.2,hH.2.2.1,hH.2.2.2⟩
      (fun v hv=>⟨hHA v hv,hHA v hv⟩) r hr L t hL hF hcount hbudget
  have hsp:∀ v z,
      (if Sum.inr (v,z)∈ordinaryWheelResources C then (1:ℤ) else 0)-
        (if Sum.inr (v,z)∈ordinaryWheelResources C' then 1 else 0)=
      (if v=x∧z=u then 1 else 0)-(if v=y∧z=u then 1 else 0):=by
    intro v z
    have hh:=hspoke v z
    omega
  let D:OrdinaryVertexWheelPair Q F H r x y a b u:=
    ⟨C,C',hCu,hC'u,hCxa,hCxb,hC'ya,hC'yb,hmap,hsupport,hrim,hsp⟩
  refine ⟨D,?_⟩
  intro v hv
  have hv':v∈(ordinaryWheelRim C).support∧v∉({x,a,b}:Finset V):=by
    simpa only [rootWheelInternal,Finset.mem_sdiff,Set.mem_toFinset] using hv
  exact (hclass v hv'.1).resolve_left hv'.2

 theorem simultaneous_ordinary_vertex_wheel_pairs (Q F:SimpleGraph V) (H:V→U→Prop)
    (A:I→Finset V) (W Ω:Finset V) (hAΩ:∀ i,A i⊆Ω)
    (x y a b:I→V) (u:I→U)
    (hxy:∀ i,x i≠y i) (hab:∀ i,a i≠b i) (haΩ:∀ i,a i∈Ω) (hbΩ:∀ i,b i∈Ω)
    (hxa:∀ i,Q.Adj (x i) (a i)) (hxb:∀ i,Q.Adj (x i) (b i))
    (hya:∀ i,Q.Adj (y i) (a i)) (hyb:∀ i,Q.Adj (y i) (b i))
    (hFroot:∀ i,∀ v∈({x i,a i,b i}:Finset V),∀ w∈({x i,a i,b i}:Finset V),¬F.Adj v w)
    (hFy:∀ i,¬F.Adj (y i) (a i)∧¬F.Adj (y i) (b i))
    (hH:∀ i,H (x i) (u i)∧H (y i) (u i)∧H (a i) (u i)∧H (b i) (u i))
    (hHA:∀ i,∀ v∈A i,H v (u i))
    (r:ℕ) (hr:4≤r) (L t:ℝ) (hL:0≤L) (hF:∀ v,(F.degree v:ℝ)≤L)
    (hcount:∀ i,∀ v∈Ω,∀ w∈Ω,t≤((A i∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hbudget:W.card+Fintype.card I*r+((r:ℝ)+4)*(L+1)<t):
    ∃ D:∀ i,OrdinaryVertexWheelPair Q F H r (x i) (y i) (a i) (b i) (u i),
      (∀ i,∀ v∈rootWheelInternal (D i).first (x i) (a i) (b i),v∈A i∧v∉W∧v≠y i) ∧
      ∀ i j,i≠j→Disjoint (rootWheelInternal (D i).first (x i) (a i) (b i))
        (rootWheelInternal (D j).first (x j) (a j) (b j)):=by
  let C:=Σ i,OrdinaryVertexWheelPair Q F H r (x i) (y i) (a i) (b i) (u i)
  let S:C→Finset V:=fun c=>rootWheelInternal c.2.first (x c.1) (a c.1) (b c.1)
  let Good:I→C→Prop:=fun i c=>c.1=i∧∀ v∈S c,v∈A i∧v∉W∧v≠y i
  have hchoose:∀ i,∀ B:Finset V,B.card≤(∅:Finset V).card+Fintype.card I*r→
      ∃ c,Good i c∧(S c).card≤r∧Disjoint (S c) B:=by
    intro i B hB
    have hBr:(B.card:ℝ)≤Fintype.card I*r:=by exact_mod_cast (by simpa using hB)
    have hWB:((W∪B).card:ℝ)≤W.card+Fintype.card I*r:=by
      have hu:((W∪B).card:ℝ)≤W.card+B.card:=by exact_mod_cast Finset.card_union_le W B
      linarith only [hu,hBr]
    obtain ⟨D,hD⟩:=ordinary_vertex_wheel_pair Q F H (A i) (W∪B) Ω (hAΩ i)
      (x i) (y i) (a i) (b i) (u i) (hxy i) (hab i) (haΩ i) (hbΩ i)
      (hxa i) (hxb i) (hya i) (hyb i) (hFroot i) (hFy i) (hH i) (hHA i)
      r hr L t hL hF (hcount i) (by linarith only [hWB,hbudget])
    refine ⟨⟨i,D⟩,⟨rfl,?_⟩,rootWheelInternal_card D.first _ _ _,?_⟩
    · intro v hv
      have hh:=hD v hv
      exact ⟨hh.1,fun hw=>hh.2.1 (Finset.mem_union_left _ hw),hh.2.2⟩
    · apply Finset.disjoint_left.mpr
      intro v hv hb
      exact (hD v hv).2.1 (Finset.mem_union_right _ hb)
  obtain ⟨f,hf,hd⟩:=finite_disjoint_choices S Good ∅ r hchoose
  have he (i:I):(f i).1=i:=(hf i).1.1
  let D:∀ i,OrdinaryVertexWheelPair Q F H r (x i) (y i) (a i) (b i) (u i):=
    fun i=>(he i) ▸ (f i).2
  have htransport (j i:I) (heq:j=i)
      (d:OrdinaryVertexWheelPair Q F H r (x j) (y j) (a j) (b j) (u j)):
      rootWheelInternal (heq ▸ d).first (x i) (a i) (b i)=
        rootWheelInternal d.first (x j) (a j) (b j):=by
    subst i
    rfl
  have hS (i:I):rootWheelInternal (D i).first (x i) (a i) (b i)=S (f i):=
    htransport (f i).1 i (he i) (f i).2
  refine ⟨D,?_,?_⟩
  · intro i v hv
    rw [hS] at hv
    exact (hf i).1.2 v hv
  · intro i j hij
    rw [hS,hS]
    exact hd i j hij

end Oberwolfach
