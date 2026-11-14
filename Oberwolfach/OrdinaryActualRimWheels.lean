module

public import Oberwolfach.TransformerActualData
public import Oberwolfach.OrdinaryRimWheelFamilies

@[expose] public section

/-! Actual rim-edge wheel pairs. The four extra hub neighbours are
computed from the shifted incidence permutation, after both kinds of
paths have been selected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 structure OrdinaryActualRimWheels (G Q F:SimpleGraph V) (H₀ H:V→U→Prop)
    (φ:V→V) (r:ℕ) (B:Finset U)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v))
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c)) where
  hub : G.edgeFinset↪U
  first : G.edgeFinset→OrdinaryWheel Q F H r
  second : G.edgeFinset→OrdinaryWheel Q F H r
  hub_avoid : ∀ e,hub e∉B
  attachments : ∀ e,∀ v∈transformerHubAttachments G σ
    (transformerRimEndpoint G Q H₀ p) (transformerSpokeEndpoint G Q H₀ b p) e,H v (hub e)
  first_hub : ∀ e,ordinaryWheelHub (first e)=hub e
  second_hub : ∀ e,ordinaryWheelHub (second e)=hub e
  first_support : ∀ e v,v∈(ordinaryWheelRim (first e)).support↔
    v=e.val.out.1∨v=e.val.out.2∨v∈(p (.inl e)).2.2.support
  second_support : ∀ e v,v∈(ordinaryWheelRim (second e)).support↔
    v=φ e.val.out.1∨v=φ e.val.out.2∨v∈(p (.inl e)).2.2.support
  first_disjoint : ∀ e f,e≠f→Disjoint (ordinaryWheelResources (first e)) (ordinaryWheelResources (first f))
  second_disjoint : ∀ e f,e≠f→Disjoint (ordinaryWheelResources (second e)) (ordinaryWheelResources (second f))
  rim_difference : ∀ i e,
    (if Sum.inl e∈ordinaryWheelResources (first i) then (1:ℤ) else 0)-
      (if Sum.inl e∈ordinaryWheelResources (second i) then 1 else 0)=
    (if e=s(i.val.out.1,i.val.out.2) then 1 else 0)+
      (if e=s(i.val.out.1,(p (.inl i)).1) then 1 else 0)+
      (if e=s(i.val.out.2,(p (.inl i)).2.1) then 1 else 0)-
      (if e=s(φ i.val.out.1,φ i.val.out.2) then 1 else 0)-
      (if e=s(φ i.val.out.1,(p (.inl i)).1) then 1 else 0)-
      (if e=s(φ i.val.out.2,(p (.inl i)).2.1) then 1 else 0)
  spoke_difference : ∀ i v z,
    (if Sum.inr (v,z)∈ordinaryWheelResources (first i) then (1:ℤ) else 0)-
      (if Sum.inr (v,z)∈ordinaryWheelResources (second i) then 1 else 0)=
    (if v=i.val.out.1∧z=hub i then 1 else 0)+(if v=i.val.out.2∧z=hub i then 1 else 0)-
      (if v=φ i.val.out.1∧z=hub i then 1 else 0)-(if v=φ i.val.out.2∧z=hub i then 1 else 0)

 theorem ordinary_actual_rim_wheels (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v))
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (r:ℕ) (hr:3≤r) (R:Finset V) (B:Finset U)
    (hroot:∀ v∈G.support,v∈R∧φ v∈R)
    (hQ:G≤Q) (hφQ:∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))
    (hcross:∀ v∈G.support,∀ w∈G.support,φ v≠w)
    (hφedge:Function.Injective (fun e:G.edgeFinset=>s(φ e.val.out.1,φ e.val.out.2)))
    (hpath:∀ e:G.edgeFinset,(p (.inl e)).2.2.IsPath∧(p (.inl e)).2.2.length=r-3)
    (hends:∀ e:G.edgeFinset,Q.Adj e.val.out.1 (p (.inl e)).1 ∧
      Q.Adj (φ e.val.out.1) (p (.inl e)).1 ∧ Q.Adj e.val.out.2 (p (.inl e)).2.1 ∧
      Q.Adj (φ e.val.out.2) (p (.inl e)).2.1)
    (havoid:∀ i,∀ v∈(p i).2.2.support,v∉R)
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)
    (hFF:∀ i j,∀ v∈(p i).2.2.support,∀ w∈(p j).2.2.support,¬F.Adj v w)
    (hFR:∀ i,∀ v∈(p i).2.2.support,∀ w∈R,¬F.Adj v w)
    (hFroots:∀ e:G.edgeFinset,∀ v∈({e.val.out.1,e.val.out.2,φ e.val.out.1,φ e.val.out.2}:Finset V),
      ∀ w∈({e.val.out.1,e.val.out.2,φ e.val.out.1,φ e.val.out.2}:Finset V),¬F.Adj v w)
    (t:ℝ) (hhubs:∀ S:Finset V,S.card≤r+6→(∀ v∈S,∀ w∈S,¬F.Adj v w)→
      t≤((common (Finset.univ:Finset U) S (fun v=>Finset.univ.filter (H v))).card:ℝ))
    (hbudget:B.card+G.edgeFinset.card<t):
    Nonempty (OrdinaryActualRimWheels G Q F H₀ H φ r B b σ p):=by
  let a:=transformerRimEndpoint G Q H₀ p
  let z:=transformerSpokeEndpoint G Q H₀ b p
  let T:=transformerHubAttachments G σ a z
  let P:Finset V:=Finset.univ.biUnion (fun i=>(p i).2.2.support.toFinset)
  have hm (i) (v) (hv:v∈(p i).2.2.support):v∈P:=
    Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,List.mem_toFinset.mpr hv⟩
  have ha (d:Σ v,G.neighborSet v):a d∈P:=hm _ _ (graphPathEndpoint_mem _ _)
  have hz (d:Σ v,G.neighborSet v):z d∈P:=hm _ _ (graphPathEndpoint_mem _ _)
  have hTP (e:G.edgeFinset):T e⊆P:=by
    intro v hv
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
    rcases Finset.mem_insert.mp hi with he|he
    · exact he ▸ ha _
    · exact (Finset.mem_singleton.mp he) ▸ hz _
  have hPF:∀ v∈P,∀ w∈P,¬F.Adj v w:=by
    intro v hv w hw
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
    obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hw
    exact hFF i j v (List.mem_toFinset.mp hi) w (List.mem_toFinset.mp hj)
  have hPR:∀ v∈P,∀ w∈R,¬F.Adj v w:=by
    intro v hv w hw
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
    exact hFR i v (List.mem_toFinset.mp hi) w hw
  have hRoots (e:G.edgeFinset):e.val.out.1∈R∧e.val.out.2∈R∧φ e.val.out.1∈R∧φ e.val.out.2∈R:=by
    have he:=edge_out_adj G e
    exact ⟨(hroot _ he.mem_support_left).1,(hroot _ he.mem_support_right).1,
      (hroot _ he.mem_support_left).2,(hroot _ he.mem_support_right).2⟩
  have hS (e:G.edgeFinset):∀ v∈({e.val.out.1,e.val.out.2,φ e.val.out.1,φ e.val.out.2}∪T e∪
      (p (.inl e)).2.2.support.toFinset:Finset V),
      ∀ w∈({e.val.out.1,e.val.out.2,φ e.val.out.1,φ e.val.out.2}∪T e∪
      (p (.inl e)).2.2.support.toFinset:Finset V),¬F.Adj v w:=by
    let Z:Finset V:={e.val.out.1,e.val.out.2,φ e.val.out.1,φ e.val.out.2}
    have hZR:Z⊆R:=by
      intro v hv
      simp only [Z,Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl|rfl|rfl
      · exact (hRoots e).1
      · exact (hRoots e).2.1
      · exact (hRoots e).2.2.1
      · exact (hRoots e).2.2.2
    have hsplit:∀ v∈(Z∪T e∪(p (.inl e)).2.2.support.toFinset),v∈Z∨v∈P:=by
      intro v hv
      rcases Finset.mem_union.mp hv with hv|hv
      · rcases Finset.mem_union.mp hv with hv|hv
        · exact Or.inl hv
        · exact Or.inr (hTP e hv)
      · exact Or.inr (hm _ _ (List.mem_toFinset.mp hv))
    intro v hv w hw
    rcases hsplit v hv with hv|hv <;> rcases hsplit w hw with hw|hw
    · exact hFroots e v hv w hw
    · exact fun hh=>hPR w hw v (hZR hv) hh.symm
    · exact hPR v hv w (hZR hw)
    · exact hPF v hv w hw
  have hinj:Function.Injective (fun e:G.edgeFinset=>s(e.val.out.1,e.val.out.2)):=by
    intro e f he
    apply Subtype.ext
    have hee:s(e.val.out.1,e.val.out.2)=e.val:=by rw [Sym2.mk];exact e.val.out_eq
    have hff:s(f.val.out.1,f.val.out.2)=f.val:=by rw [Sym2.mk];exact f.val.out_eq
    exact hee.symm.trans (he.trans hff)
  have hcross' (e:G.edgeFinset):φ e.val.out.1≠e.val.out.1∧φ e.val.out.1≠e.val.out.2∧
      φ e.val.out.2≠e.val.out.1∧φ e.val.out.2≠e.val.out.2:=by
    have he:=edge_out_adj G e
    exact ⟨hcross _ he.mem_support_left _ he.mem_support_left,
      hcross _ he.mem_support_left _ he.mem_support_right,
      hcross _ he.mem_support_right _ he.mem_support_left,
      hcross _ he.mem_support_right _ he.mem_support_right⟩
  obtain ⟨h,W,W',hT,hh,hs,hs',hd,hd',hrim,hspoke⟩:=ordinary_rim_wheel_families Q F H r hr R B T
    (fun e:G.edgeFinset=>e.val.out.1) (fun e=>e.val.out.2) (fun e=>φ e.val.out.1) (fun e=>φ e.val.out.2)
    (fun e=>p (.inl e)) hRoots (fun e=>hQ (edge_out_adj G e)) (fun e=>hφQ _ _ (edge_out_adj G e))
    hcross' hpath hends (fun e=>havoid (.inl e))
    (fun e f he=>hdis (.inl e) (.inl f) (fun hh=>he (Sum.inl.inj hh)))
    (fun e=>transformerHubAttachments_card G σ a z e) hS hinj hφedge t hhubs
    (by simpa only [Fintype.card_coe] using hbudget)
  exact ⟨⟨h,W,W',fun e=>(hT e).1,fun e=>(hT e).2,fun e=>(hh e).1,fun e=>(hh e).2,
    hs,hs',hd,hd',hrim,hspoke⟩⟩

 theorem OrdinaryActualRimWheels.root_hub_adjacency
    {G Q F:SimpleGraph V} {H₀ H:V→U→Prop} {φ:V→V} {r:ℕ} {B:Finset U}
    {b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2)} {σ:∀ v,Equiv.Perm (G.neighborSet v)}
    {p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c)}
    (E:OrdinaryActualRimWheels G Q F H₀ H φ r B b σ p):
    ∀ e,H e.val.out.1 (E.hub e)∧H (φ e.val.out.1) (E.hub e)∧
      H e.val.out.2 (E.hub e)∧H (φ e.val.out.2) (E.hub e):=by
  intro e
  have h1:∀ v∈(ordinaryWheelRim (E.first e)).support,H v (E.hub e):=by
    intro v hv
    have hh:H v (ordinaryWheelHub (E.first e)):=(E.first e).property.1 v hv
    rw [E.first_hub] at hh;exact hh
  have h2:∀ v∈(ordinaryWheelRim (E.second e)).support,H v (E.hub e):=by
    intro v hv
    have hh:H v (ordinaryWheelHub (E.second e)):=(E.second e).property.1 v hv
    rw [E.second_hub] at hh;exact hh
  exact ⟨h1 _ ((E.first_support e _).mpr (Or.inl rfl)),h2 _ ((E.second_support e _).mpr (Or.inl rfl)),
    h1 _ ((E.first_support e _).mpr (Or.inr (Or.inl rfl))),h2 _ ((E.second_support e _).mpr (Or.inr (Or.inl rfl)))⟩

end Oberwolfach
