module

public import Oberwolfach.BoundedMatchingOnSubset
public import Oberwolfach.EndpointParentMatching

@[expose] public section

/-! The original parent weights for the triangle endpoint construction
follow from the three-quarter degree assumption by the self-contained bounded
fractional matching theorem. They are chosen before any sampled subgraph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem endpoint_parent_matching_exists (P:SimpleGraph V) (A:Finset V) (x:V)
    (hn:32≤A.card)
    (hdeg:∀ v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)) :
    ∃ weight:Sym2 V→ℝ,
      (∀ v∈A∩P.neighborFinset x,∀ w∈A∩P.neighborFinset x,
        0≤weight s(v,w) ∧ weight s(v,w)≤40/A.card) ∧
      (∀ v∈A∩P.neighborFinset x,∑ w∈A∩P.neighborFinset x,weight s(v,w)=1) ∧
      (∀ v w,¬P.Adj v w → weight s(v,w)=0) ∧
      (∀ F:SimpleGraph V,∀ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet,
        (1/30:ℝ)/A.card≤weight e ∧ weight e≤40/A.card) := by
  let S:=A∩P.neighborFinset x
  have hS:S⊆A:=Finset.inter_subset_left
  have hsize:(3/4:ℝ)*A.card≤S.card:=hdeg x (Finset.mem_insert_self _ _)
  have hA:(0:ℝ)<A.card:=by exact_mod_cast (show 0<A.card by omega)
  have hSpos:(0:ℝ)<S.card:=(mul_pos (by norm_num) hA).trans_le hsize
  have hSA:(S.card:ℝ)≤A.card:=Nat.cast_le.mpr (Finset.card_le_card hS)
  have hlarge:4/(1/6:ℝ)≤S.card:=by
    have hh:(32:ℝ)≤A.card:=by exact_mod_cast hn
    linarith
  have hlocal (v:V) (hv:v∈S):(1/2+(1/6:ℝ))*S.card≤((S∩P.neighborFinset v).card:ℝ):=by
    have hc:=Finset.card_inter_add_card_union (A∩P.neighborFinset v) S
    have hu:(A∩P.neighborFinset v)∪S⊆A:=Finset.union_subset Finset.inter_subset_left hS
    have huc:=Finset.card_le_card hu
    have he:(A∩P.neighborFinset v)∩S=S∩P.neighborFinset v:=by
      ext z;simp only [Finset.mem_inter];constructor
      · exact fun h=>⟨h.2,h.1.2⟩
      · exact fun h=>⟨⟨hS h.1,h.2⟩,h.1⟩
    rw [he] at hc
    have hc':((S∩P.neighborFinset v).card:ℝ)+((A∩P.neighborFinset v)∪S).card=
        (A∩P.neighborFinset v).card+S.card:=by exact_mod_cast hc
    have huc':(((A∩P.neighborFinset v)∪S).card:ℝ)≤A.card:=by exact_mod_cast huc
    have hd:=hdeg v (Finset.mem_insert_of_mem (hS hv))
    linarith
  obtain ⟨weight,hw,hsum,hzero,hlo⟩:=bounded_fractional_matching_on_subset P S (1/6)
    (by norm_num) (by norm_num) hlarge hlocal
  have hupper:5/((1/6:ℝ)*S.card)≤40/A.card:=by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hSpos) hA).mpr
    nlinarith only [hsize]
  have hlower:(1/30:ℝ)/A.card≤(1/6:ℝ)/(5*S.card):=by
    apply (div_le_div_iff₀ hA (mul_pos (by norm_num) hSpos)).mpr
    nlinarith only [hSA]
  refine ⟨weight,(fun v hv w hw'=>⟨(hw v hv w hw').1,(hw v hv w hw').2.trans hupper⟩),hsum,hzero,?_⟩
  intro F e he
  induction e using Sym2.ind with
  | _ v w =>
    exact ⟨hlower.trans (hlo v he.1 w he.2.1 he.2.2.2.2.1),
      (hw v he.1 w he.2.1).2.trans hupper⟩

end Oberwolfach
