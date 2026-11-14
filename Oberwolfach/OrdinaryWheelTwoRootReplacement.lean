module

public import Oberwolfach.GraphTwoRootReplacement
public import Oberwolfach.RootWheelCaps

@[expose] public section

/-! Replace both ends of a rim edge in an actual wheel. Only the final
three changed rim edges need to be host edges. The intermediate cross
edge used in the signed calculation is not assumed to be present. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

theorem ordinary_wheel_two_root_replacement (W:OrdinaryWheel Q F H r) (x y x' y' a b:V)
    (hxy:(ordinaryWheelRim W).Adj x y) (hxa:(ordinaryWheelRim W).Adj x a)
    (hyb:(ordinaryWheelRim W).Adj y b) (hya:y≠a) (hxb:x≠b)
    (hx':x'∉(ordinaryWheelRim W).support) (hy':y'∉(ordinaryWheelRim W).support) (hnew:x'≠y')
    (hQxy:Q.Adj x' y') (hQxa:Q.Adj x' a) (hQyb:Q.Adj y' b)
    (hH:H x' (ordinaryWheelHub W)∧H y' (ordinaryWheelHub W))
    (hFnew:¬F.Adj x' y')
    (hF:∀ v∈(ordinaryWheelRim W).support,v≠x→v≠y→¬F.Adj x' v∧¬F.Adj y' v):
    ∃ W':OrdinaryWheel Q F H r,
      ordinaryWheelRim W'=((ordinaryWheelRim W).map (Equiv.swap x x').toEmbedding).map (Equiv.swap y y').toEmbedding ∧
      ordinaryWheelHub W'=ordinaryWheelHub W ∧
      (∀ v,v∈(ordinaryWheelRim W').support↔v=x'∨v=y'∨(v∈(ordinaryWheelRim W).support∧v≠x∧v≠y)) ∧
      (∀ e:Sym2 V,
        (if Sum.inl e∈ordinaryWheelResources W then (1:ℤ) else 0)-
          (if Sum.inl e∈ordinaryWheelResources W' then 1 else 0)=
        (if e=s(x,y) then 1 else 0)+(if e=s(x,a) then 1 else 0)+(if e=s(y,b) then 1 else 0)-
          (if e=s(x',y') then 1 else 0)-(if e=s(x',a) then 1 else 0)-(if e=s(y',b) then 1 else 0)) ∧
      (∀ v z,
        (if Sum.inr (v,z)∈ordinaryWheelResources W then (1:ℤ) else 0)-
          (if Sum.inr (v,z)∈ordinaryWheelResources W' then 1 else 0)=
        (if v=x∧z=ordinaryWheelHub W then 1 else 0)+(if v=y∧z=ordinaryWheelHub W then 1 else 0)-
          (if v=x'∧z=ordinaryWheelHub W then 1 else 0)-(if v=y'∧z=ordinaryWheelHub W then 1 else 0)):=by
  let C:=((ordinaryWheelRim W).map (Equiv.swap x x').toEmbedding).map (Equiv.swap y y').toEmbedding
  have hNx:=(ordinaryWheel_root_neighbors W x y a hya hxy hxa)
  have hNy:=(ordinaryWheel_root_neighbors W y x b hxb hxy.symm hyb)
  have hC:IsEmbeddedCycle C r:=((W.val.1.val.property).map (Equiv.swap x x').toEmbedding).map
    (Equiv.swap y y').toEmbedding
  have hCQ:C≤Q:=graph_two_root_subgraph _ Q x y x' y' a b W.val.1.property hxy hya hxb
    hx' hy' hnew hNx hNy hQxy hQxa hQyb
  have hs (v:V):v∈C.support↔v=x'∨v=y'∨(v∈(ordinaryWheelRim W).support∧v≠x∧v≠y):=
    graph_two_root_support _ x y x' y' hxy.ne hxy.mem_support_left hxy.mem_support_right hx' hy' hnew v
  have hCH:∀ v∈C.support,H v (ordinaryWheelHub W):=by
    intro v hv
    rcases (hs v).mp hv with h|h|hv
    · rw [h];exact hH.1
    · rw [h];exact hH.2
    · exact W.property.1 v hv.1
  have hCF:∀ v∈C.support,∀ w∈C.support,¬F.Adj v w:=by
    intro v hv w hw
    rcases (hs v).mp hv with hv|hv|hv <;> rcases (hs w).mp hw with hw|hw|hw
    · rw [hv,hw];exact F.loopless.irrefl _
    · rw [hv,hw];exact hFnew
    · rw [hv];exact (hF w hw.1 hw.2.1 hw.2.2).1
    · rw [hv,hw];exact fun h=>hFnew h.symm
    · rw [hv,hw];exact F.loopless.irrefl _
    · rw [hv];exact (hF w hw.1 hw.2.1 hw.2.2).2
    · rw [hw];exact fun h=>(hF v hv.1 hv.2.1 hv.2.2).1 h.symm
    · rw [hw];exact fun h=>(hF v hv.1 hv.2.1 hv.2.2).2 h.symm
    · exact W.property.2 v hv.1 w hw.1
  let W':OrdinaryWheel Q F H r:=⟨(⟨⟨C,hC⟩,hCQ⟩,ordinaryWheelHub W),hCH,hCF⟩
  have hWr:ordinaryWheelRim W'=C:=rfl
  have hWu:ordinaryWheelHub W'=ordinaryWheelHub W:=rfl
  refine ⟨W',rfl,hWu,hs,?_,?_⟩
  · intro e
    simp only [ordinaryWheelResources_rim,hWr]
    simpa only [SimpleGraph.mem_edgeFinset] using
      graph_two_root_indicator (ordinaryWheelRim W) x y x' y' a b hxy hya hxb hx' hy' hnew hNx hNy e
  · intro v z
    simp only [ordinaryWheelResources_spoke,hWr,hWu,hs]
    have hx:=hxy.mem_support_left
    have hy:=hxy.mem_support_right
    have hxy':x≠y:=hxy.ne
    by_cases hz:z=ordinaryWheelHub W
    · subst z
      simp only [true_and]
      by_cases hvx:v=x <;> by_cases hvy:v=y <;> by_cases hvx':v=x' <;> by_cases hvy':v=y' <;>
        by_cases hv:v∈(ordinaryWheelRim W).support
      all_goals simp_all
      all_goals simp_all [eq_comm]
      all_goals obtain ⟨w,hw⟩:=hv
      all_goals first | exact hx' hw | exact hx' w hw | exact hy' hw | exact hy' w hw
    · simp only [Ne.symm hz,hz,false_and,and_false,ite_false,sub_self,add_zero,sub_zero]

end Oberwolfach
