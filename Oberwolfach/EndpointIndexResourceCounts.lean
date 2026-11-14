module

public import Oberwolfach.EndpointIndexResources

@[expose] public section

/-! Exact candidate families and resource incidences for the unordered
edge sum in the endpoint index potential. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem endpointIndexCandidates_card (E:SimpleGraph V) (A:Finset V)
    (hE:∀ e∈E.edgeSet,∀ v∈e,v∈A):E.edgeFinset.card≤A.card^2:=by
  have hsub:E.edgeFinset⊆(A.product A).image (fun p:V×V=>s(p.1,p.2)):=by
    intro e he
    induction e using Sym2.ind with
    | _ v w=>
      have hh:=hE s(v,w) (SimpleGraph.mem_edgeFinset.mp he)
      exact Finset.mem_image.mpr ⟨(v,w),Finset.mem_product.mpr ⟨hh v (by simp),hh w (by simp)⟩,rfl⟩
  calc
    _≤((A.product A).image (fun p:V×V=>s(p.1,p.2))).card:=Finset.card_le_card hsub
    _≤(A.product A).card:=Finset.card_image_le
    _=A.card^2:=by
      convert Finset.card_product A A using 1 <;> simp only [pow_two] <;> congr!

theorem endpointIndexCandidates_incidence (E:SimpleGraph V) (A:Finset V)
    (hE:∀ e∈E.edgeSet,∀ v∈e,v∈A) (hA:0<A.card) (x:V) (u:U) (f:Sym2 V⊕(V×U)):
    (E.edgeFinset.filter (fun e=>f∈endpointIndexResources x u e)).card≤3*A.card:=by
  cases f with
  | inl f=>
    induction f using Sym2.ind with
    | _ a b=>
      let J:=(({a,b}:Finset V).product A).image (fun p:V×V=>s(p.1,p.2))
      have hsub:E.edgeFinset.filter (fun e=>Sum.inl s(a,b)∈endpointIndexResources x u e)⊆insert s(a,b) J:=by
        intro e he
        obtain ⟨he,hr⟩:=Finset.mem_filter.mp he
        rcases (endpointIndexResources_rim x u e s(a,b)).mp hr with hf|⟨v,hv,hf⟩
        · exact Finset.mem_insert.mpr (Or.inl hf.symm)
        · obtain ⟨w,hew⟩:=Sym2.mem_iff_exists.mp hv
          have hw:w∈A:=hE e (SimpleGraph.mem_edgeFinset.mp he) w (by rw [hew];simp)
          have hv':v∈({a,b}:Finset V):=by
            rcases Sym2.eq_iff.mp hf with hh|hh
            · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hh.2.symm)
            · exact Finset.mem_insert.mpr (Or.inl hh.1.symm)
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(v,w),Finset.mem_product.mpr ⟨hv',hw⟩,hew.symm⟩)
      have hc:=Finset.card_le_card hsub
      have hi:=Finset.card_insert_le s(a,b) J
      have hj:J.card≤({a,b}:Finset V).card*A.card:=Finset.card_image_le.trans_eq (Finset.card_product _ _)
      have ht:({a,b}:Finset V).card≤2:=Finset.card_le_two
      nlinarith only [hc,hi,hj,Nat.mul_le_mul_right A.card ht,hA]
  | inr av=>
    let J:=A.image (fun w=>s(av.1,w))
    have hsub:E.edgeFinset.filter (fun e=>Sum.inr av∈endpointIndexResources x u e)⊆J:=by
      intro e he
      obtain ⟨he,hr⟩:=Finset.mem_filter.mp he
      have hv:av.1∈e:=((endpointIndexResources_spoke x av.1 u av.2 e).mp hr).2
      obtain ⟨w,hew⟩:=Sym2.mem_iff_exists.mp hv
      have hw:w∈A:=hE e (SimpleGraph.mem_edgeFinset.mp he) w (by rw [hew];simp)
      exact Finset.mem_image.mpr ⟨w,hw,hew.symm⟩
    have hc:(_ :ℕ)≤A.card:=(Finset.card_le_card hsub).trans Finset.card_image_le
    omega

theorem endpointIndexCandidates_weight_bounds (E:SimpleGraph V) (A:Finset V)
    (hE:∀ e∈E.edgeSet,∀ v∈e,v∈A) (hA:0<A.card) (x:V) (u:U)
    (w:↥E.edgeFinset→ℝ) (M:ℝ) (hM:0≤M) (hw:∀ e,0≤w e∧w e≤M):
    (∑ e,w e)≤M*A.card^2 ∧
    ∀ f:Sym2 V⊕(V×U),(∑ e,if f∈endpointIndexResources x u e.val then w e else 0)≤M*(3*A.card):=by
  constructor
  · calc
      _≤∑ _e:↥E.edgeFinset,M:=Finset.sum_le_sum (fun e _=>(hw e).2)
      _=M*E.edgeFinset.card:=by simp [mul_comm]
      _≤_:=mul_le_mul_of_nonneg_left (by exact_mod_cast endpointIndexCandidates_card E A hE) hM
  · intro f
    have hcount:(Finset.univ.filter (fun e:↥E.edgeFinset=>f∈endpointIndexResources x u e.val)).card=
        (E.edgeFinset.filter (fun e=>f∈endpointIndexResources x u e)).card:=by
      have hh:=Finset.sum_coe_sort E.edgeFinset
        (fun e=>if f∈endpointIndexResources x u e then (1:ℕ) else 0)
      simpa using hh
    rw [←Finset.sum_filter]
    calc
      _≤∑ _e∈Finset.univ.filter (fun e:↥E.edgeFinset=>f∈endpointIndexResources x u e.val),M:=
        Finset.sum_le_sum (fun e _=>(hw e).2)
      _=M*(E.edgeFinset.filter (fun e=>f∈endpointIndexResources x u e)).card:=by simp only [Finset.sum_const,nsmul_eq_mul,hcount];ring
      _≤_:=mul_le_mul_of_nonneg_left (by exact_mod_cast endpointIndexCandidates_incidence E A hE hA x u f) hM

end Oberwolfach
