module

public import Oberwolfach.TransformerRimPaths
public import Oberwolfach.OrdinaryEdgePathWheels

@[expose] public section

/-! The rim-edge transformer gadget is constructed inside its actual
host from local common-neighbour inequalities. Extra prescribed labels
at the fresh hub are retained, with the source bound r+6. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_rim_edge_pair (Q F:SimpleGraph V) (H:V→U→Prop)
    (A W Ω Z:Finset V) (B:Finset U) (hAΩ:A⊆Ω)
    (x y x' y':V) (hxy:Q.Adj x y) (hxy':Q.Adj x' y')
    (hx'x:x'≠x) (hx'y:x'≠y) (hy'x:y'≠x) (hy'y:y'≠y)
    (hroots:x∈Z∧y∈Z∧x'∈Z∧y'∈Z) (hZcard:Z.card≤8)
    (hΩ:x∈Ω∧y∈Ω∧x'∈Ω∧y'∈Ω)
    (hZ:∀ v∈Z,∀ w∈Z,¬F.Adj v w)
    (r:ℕ) (hr:4≤r) (L b bH:ℝ) (hL:0≤L) (hF:∀ v,(F.degree v:ℝ)≤L)
    (hcount:∀ v∈Ω,∀ w∈Ω,b≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hthree:r=4→∀ a∈A,b≤(((A∩Q.neighborFinset a)∩Q.neighborFinset y∩Q.neighborFinset y').card:ℝ))
    (hhubs:∀ S:Finset V,S.card≤r+6→(∀ v∈S,∀ w∈S,¬F.Adj v w)→
      bH≤((common (Finset.univ:Finset U) S (fun v=>Finset.univ.filter (H v))).card:ℝ))
    (hbudget:W.card+((Z.card:ℝ)+r+2)*(L+1)<b) (hhubBudget:(B.card:ℝ)<bH):
    ∃ a b',∃ p:Q.Walk a b',∃ u:U,∃ C C':OrdinaryWheel Q F H r,
      p.IsPath ∧ p.length=r-3 ∧ u∉B ∧ (∀ v∈Z,H v u) ∧
      (∀ v∈p.support,v∈A∧v∉W∧v∉Z) ∧
      ordinaryWheelHub C=u ∧ ordinaryWheelHub C'=u ∧
      (∀ v,v∈(ordinaryWheelRim C).support↔v=x∨v=y∨v∈p.support) ∧
      (∀ v,v∈(ordinaryWheelRim C').support↔v=x'∨v=y'∨v∈p.support) ∧
      (∀ e:Sym2 V,
        (if Sum.inl e∈ordinaryWheelResources C then (1:ℤ) else 0)-
          (if Sum.inl e∈ordinaryWheelResources C' then 1 else 0)=
        (if e=s(x,y) then 1 else 0)+(if e=s(x,a) then 1 else 0)+(if e=s(y,b') then 1 else 0)-
          (if e=s(x',y') then 1 else 0)-(if e=s(x',a) then 1 else 0)-(if e=s(y',b') then 1 else 0)) ∧
      (∀ v z,
        (if Sum.inr (v,z)∈ordinaryWheelResources C then (1:ℤ) else 0)-
          (if Sum.inr (v,z)∈ordinaryWheelResources C' then 1 else 0)=
        (if v=x∧z=u then 1 else 0)+(if v=y∧z=u then 1 else 0)-
          (if v=x'∧z=u then 1 else 0)-(if v=y'∧z=u then 1 else 0)):=by
  obtain ⟨a,c,p,hp,hlen,hxa,hx'a,hyc,hy'c,hclass,hind,hroot⟩:=
    transformer_rim_common_path Q F A W Ω Z hAΩ x y x' y' hroots hΩ hZ r hr L b hL hF
      hcount hthree hbudget
  let S:=Z∪p.support.toFinset
  have hSsize:S.card≤r+6:=by
    have hpCard:p.support.toFinset.card≤r-2:=by
      have hh:=List.toFinset_card_le p.support
      rw [p.length_support,hlen] at hh
      omega
    exact (Finset.card_union_le Z p.support.toFinset).trans (by omega)
  have hSF:∀ v∈S,∀ w∈S,¬F.Adj v w:=by
    intro v hv w hw
    rcases Finset.mem_union.mp hv with hv|hv <;> rcases Finset.mem_union.mp hw with hw|hw
    · exact hZ v hv w hw
    · exact fun h=>hroot w (List.mem_toFinset.mp hw) v hv h.symm
    · exact hroot v (List.mem_toFinset.mp hv) w hw
    · exact hind v (List.mem_toFinset.mp hv) w (List.mem_toFinset.mp hw)
  have hlarge:B.card<(common (Finset.univ:Finset U) S (fun v=>Finset.univ.filter (H v))).card:=by
    exact_mod_cast hhubBudget.trans_le (hhubs S hSsize hSF)
  obtain ⟨u,hu,huB⟩:=Finset.exists_mem_notMem_of_card_lt_card hlarge
  have hSH:∀ v∈S,H v u:=by
    simpa only [common,Finset.mem_filter,Finset.mem_univ,true_and] using hu
  have hrootSubset:({x,y,x',y'}:Finset V)⊆Z:=by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl|rfl|rfl
    · exact hroots.1
    · exact hroots.2.1
    · exact hroots.2.2.1
    · exact hroots.2.2.2
  have hsmall:insert x (insert y (insert x' (insert y' p.support.toFinset)))⊆S:=by
    intro v hv
    simp only [Finset.mem_insert] at hv
    rcases hv with hv|hv|hv|hv|hv
    · exact Finset.mem_union_left _ (hv.symm ▸ hroots.1)
    · exact Finset.mem_union_left _ (hv.symm ▸ hroots.2.1)
    · exact Finset.mem_union_left _ (hv.symm ▸ hroots.2.2.1)
    · exact Finset.mem_union_left _ (hv.symm ▸ hroots.2.2.2)
    · exact Finset.mem_union_right _ hv
  obtain ⟨C,C',hCu,hC'u,hCs,hC's,hrim,hspoke⟩:=ordinary_edge_path_wheels Q F H r (by omega)
    x y x' y' a c u p hp hlen hxy hxa hyc hxy' hx'a hy'c hx'x hx'y hy'x hy'y
    (fun v hv h=>(hclass v hv).2.2 (hrootSubset h))
    (fun v hv w hw=>hSF v (hsmall hv) w (hsmall hw)) (fun v hv=>hSH v (hsmall hv))
  exact ⟨a,c,p,u,C,C',hp,hlen,huB,(fun v hv=>hSH v (Finset.mem_union_left _ hv)),hclass,
    hCu,hC'u,hCs,hC's,hrim,hspoke⟩

end Oberwolfach
