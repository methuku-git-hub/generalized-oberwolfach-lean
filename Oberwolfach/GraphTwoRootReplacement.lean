module

public import Oberwolfach.GraphRootReplacement

@[expose] public section

/-! Replace the two ends of a prescribed cycle edge. The intermediate
edge cancels exactly, leaving the root edge and two attachment edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem sym2_fixed_endpoint_injective (x:V):Function.Injective (fun a=>s(x,a)):=by
  intro a b h
  rcases Sym2.eq_iff.mp h with ⟨_,hab⟩|⟨hxb,hax⟩
  · exact hab
  · exact hax.trans hxb

theorem int_indicator_pair {E:Type} [DecidableEq E] (e a b:E) (hab:a≠b):
    (if e∈({a,b}:Finset E) then (1:ℤ) else 0)=
      (if e=a then 1 else 0)+(if e=b then 1 else 0):=by
  by_cases ha:e=a <;> by_cases hb:e=b <;> simp_all

theorem graphRootEdges_pair (C:SimpleGraph V) (x z a b:V)
    (hN:C.neighborFinset x={a,b}):graphRootEdges C x z={s(z,a),s(z,b)}:=by
  unfold graphRootEdges
  rw [hN]
  simp

theorem graph_swap_other_root_neighbors (C:SimpleGraph V) (x x' y b:V)
    (hxy:x≠y) (hxb:x≠b) (hx':x'∉C.support)
    (hxyC:C.Adj x y) (hyb:C.Adj y b) (hN:C.neighborFinset y={x,b}):
    (C.map (Equiv.swap x x').toEmbedding).neighborFinset y={x',b}:=by
  have hyx':y≠x':=fun h=>hx' (h ▸ hxyC.mem_support_right)
  have hbx':b≠x':=fun h=>hx' (h ▸ hyb.mem_support_right)
  ext a
  rw [SimpleGraph.mem_neighborFinset,graph_swap_adj,
    Equiv.swap_apply_of_ne_of_ne hxy.symm hyx']
  rw [←C.mem_neighborFinset y (Equiv.swap x x' a),hN]
  simp only [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro (h|h)
    · left
      have hh:=congrArg (Equiv.swap x x') h
      simpa only [Equiv.swap_apply_self,Equiv.swap_apply_left] using hh
    · right
      have hh:=congrArg (Equiv.swap x x') h
      simpa only [Equiv.swap_apply_self,Equiv.swap_apply_of_ne_of_ne hxb.symm hbx'] using hh
  · rintro (rfl|rfl)
    · exact Or.inl (Equiv.swap_apply_right _ _)
    · exact Or.inr (Equiv.swap_apply_of_ne_of_ne hxb.symm hbx')

theorem graph_two_root_indicator (C:SimpleGraph V) (x y x' y' a b:V)
    (hxyC:C.Adj x y) (hya:y≠a) (hxb:x≠b)
    (hx':x'∉C.support) (hy':y'∉C.support) (hnew:x'≠y')
    (hNx:C.neighborFinset x={y,a}) (hNy:C.neighborFinset y={x,b}) (e:Sym2 V):
    let C':=(C.map (Equiv.swap x x').toEmbedding).map (Equiv.swap y y').toEmbedding
    (if e∈C.edgeFinset then (1:ℤ) else 0)-(if e∈C'.edgeFinset then 1 else 0)=
      (if e=s(x,y) then 1 else 0)+(if e=s(x,a) then 1 else 0)+(if e=s(y,b) then 1 else 0)-
      (if e=s(x',y') then 1 else 0)-(if e=s(x',a) then 1 else 0)-(if e=s(y',b) then 1 else 0):=by
  dsimp only
  let C₁:=C.map (Equiv.swap x x').toEmbedding
  have hyb:C.Adj y b:=by
    apply (C.mem_neighborFinset y b).mp
    rw [hNy];simp
  have hy'C₁:y'∉C₁.support:=by
    intro h
    rcases (graph_swap_root_support C x x' hxyC.mem_support_left hx' y').mp h with h|h
    · exact hnew h.symm
    · exact hy' h.1
  have hN₁:C₁.neighborFinset y={x',b}:=
    graph_swap_other_root_neighbors C x x' y b hxyC.ne hxb hx' hxyC hyb hNy
  have hx'b:x'≠b:=fun h=>hx' (h.symm ▸ hyb.mem_support_right)
  have h₀:=graph_swap_root_indicator C x x' hx' e
  have h₁:=graph_swap_root_indicator C₁ y y' hy'C₁ e
  have hN₁':@SimpleGraph.neighborFinset V C₁ y
      (@Subtype.fintype V (C₁.neighborSet y) (fun a=>Classical.propDecidable _) inferInstance)={x',b}:=by
    apply Finset.coe_injective
    simpa only [SimpleGraph.coe_neighborFinset] using congrArg (fun s:Finset V=>(s:Set V)) hN₁
  have h0x:=graphRootEdges_pair C x x y a hNx
  have h0x':=graphRootEdges_pair C x x' y a hNx
  have h1y:=graphRootEdges_pair C₁ y y x' b hN₁'
  have h1y':=graphRootEdges_pair C₁ y y' x' b hN₁'
  have hp0:=int_indicator_pair e s(x,y) s(x,a) (fun h=>hya (sym2_fixed_endpoint_injective x h))
  have hp0':=int_indicator_pair e s(x',y) s(x',a) (fun h=>hya (sym2_fixed_endpoint_injective x' h))
  have hp1:=int_indicator_pair e s(y,x') s(y,b) (fun h=>hx'b (sym2_fixed_endpoint_injective y h))
  have hp1':=int_indicator_pair e s(y',x') s(y',b) (fun h=>hx'b (sym2_fixed_endpoint_injective y' h))
  simp only [h0x,h0x',hp0,hp0'] at h₀
  simp only [h1y,h1y',hp1,hp1'] at h₁
  have hswap:s(y,x')=s(x',y):=Sym2.eq_swap
  have hswap':s(y',x')=s(x',y'):=Sym2.eq_swap
  simp only [hswap,hswap'] at h₁
  simp only [SimpleGraph.mem_edgeFinset] at h₀ h₁ ⊢
  linarith only [h₀,h₁]

theorem graph_two_root_subgraph (C Q:SimpleGraph V) (x y x' y' a b:V)
    (hCQ:C≤Q) (hxyC:C.Adj x y) (hya:y≠a) (hxb:x≠b)
    (hx':x'∉C.support) (hy':y'∉C.support) (hnew:x'≠y')
    (hNx:C.neighborFinset x={y,a}) (hNy:C.neighborFinset y={x,b})
    (hQxy:Q.Adj x' y') (hQxa:Q.Adj x' a) (hQyb:Q.Adj y' b):
    (C.map (Equiv.swap x x').toEmbedding).map (Equiv.swap y y').toEmbedding≤Q:=by
  let ρ:V↪V:=(Equiv.swap x x').toEmbedding.trans (Equiv.swap y y').toEmbedding
  have hxa:C.Adj x a:=by
    apply (C.mem_neighborFinset x a).mp;rw [hNx];simp
  have hyb:C.Adj y b:=by
    apply (C.mem_neighborFinset y b).mp;rw [hNy];simp
  have hx'y:x'≠y:=fun h=>hx' (h.symm ▸ hxyC.mem_support_right)
  have hρx:ρ x=x':=by
    change Equiv.swap y y' (Equiv.swap x x' x)=x'
    rw [Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne hx'y hnew]
  have hρy:ρ y=y':=by
    change Equiv.swap y y' (Equiv.swap x x' y)=y'
    rw [Equiv.swap_apply_of_ne_of_ne hxyC.ne.symm hx'y.symm,Equiv.swap_apply_left]
  have hfix (v:V) (hv:v∈C.support) (hvx:v≠x) (hvy:v≠y):ρ v=v:=by
    change Equiv.swap y y' (Equiv.swap x x' v)=v
    have hvx':v≠x':=fun h=>hx' (h ▸ hv)
    have hvy':v≠y':=fun h=>hy' (h ▸ hv)
    rw [Equiv.swap_apply_of_ne_of_ne hvx hvx',Equiv.swap_apply_of_ne_of_ne hvy hvy']
  have hρa:ρ a=a:=hfix a hxa.mem_support_right hxa.ne.symm hya.symm
  have hρb:ρ b=b:=hfix b hyb.mem_support_right hxb.symm hyb.ne.symm
  have hxstep (v:V) (hv:C.Adj x v):Q.Adj (ρ x) (ρ v):=by
    have hm: v∈C.neighborFinset x:=(C.mem_neighborFinset x v).mpr hv
    rw [hNx] at hm
    rcases Finset.mem_insert.mp hm with rfl|hm
    · rw [hρx,hρy];exact hQxy
    · have he:=Finset.mem_singleton.mp hm;subst v
      rw [hρx,hρa];exact hQxa
  have hystep (v:V) (hv:C.Adj y v):Q.Adj (ρ y) (ρ v):=by
    have hm: v∈C.neighborFinset y:=(C.mem_neighborFinset y v).mpr hv
    rw [hNy] at hm
    rcases Finset.mem_insert.mp hm with rfl|hm
    · rw [hρy,hρx];exact hQxy.symm
    · have he:=Finset.mem_singleton.mp hm;subst v
      rw [hρy,hρb];exact hQyb
  have hadj (v w:V) (hvw:C.Adj v w):Q.Adj (ρ v) (ρ w):=by
    by_cases hvx:v=x
    · subst v;exact hxstep w hvw
    by_cases hvy:v=y
    · subst v;exact hystep w hvw
    by_cases hwx:w=x
    · subst w;exact (hxstep v hvw.symm).symm
    by_cases hwy:w=y
    · subst w;exact (hystep v hvw.symm).symm
    rw [hfix v hvw.mem_support_left hvx hvy,hfix w hvw.mem_support_right hwx hwy]
    exact hCQ hvw
  intro v w hvw
  obtain ⟨v₁,w₁,h₁,rfl,rfl⟩:=(SimpleGraph.map_adj _ _ _ _).mp hvw
  obtain ⟨v₀,w₀,h₀,rfl,rfl⟩:=(SimpleGraph.map_adj _ _ _ _).mp h₁
  exact hadj v₀ w₀ h₀

theorem graph_two_root_support (C:SimpleGraph V) (x y x' y':V)
    (hxy:x≠y) (hx:x∈C.support) (hy:y∈C.support)
    (hx':x'∉C.support) (hy':y'∉C.support) (hnew:x'≠y') (v:V):
    v∈((C.map (Equiv.swap x x').toEmbedding).map (Equiv.swap y y').toEmbedding).support↔
      v=x'∨v=y'∨(v∈C.support∧v≠x∧v≠y):=by
  let C₁:=C.map (Equiv.swap x x').toEmbedding
  have hy₁:y∈C₁.support:=(graph_swap_root_support C x x' hx hx' y).mpr (Or.inr ⟨hy,hxy.symm⟩)
  have hy'₁:y'∉C₁.support:=by
    intro h
    rcases (graph_swap_root_support C x x' hx hx' y').mp h with h|h
    · exact hnew h.symm
    · exact hy' h.1
  rw [graph_swap_root_support C₁ y y' hy₁ hy'₁,graph_swap_root_support C x x' hx hx']
  have hx'y:x'≠y:=fun h=>hx' (h.symm ▸ hy)
  constructor
  · rintro (h|⟨h|⟨hv,hvx⟩,hvy⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨hv,hvx,hvy⟩)
  · rintro (h|h|⟨hv,hvx,hvy⟩)
    · exact Or.inr ⟨Or.inl h,h.symm ▸ hx'y⟩
    · exact Or.inl h
    · exact Or.inr ⟨Or.inr ⟨hv,hvx⟩,hvy⟩

end Oberwolfach
