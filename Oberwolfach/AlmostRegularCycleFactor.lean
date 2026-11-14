module

public import Oberwolfach.OrdinaryLocalFactorFromWeights
public import Oberwolfach.AlmostSpanningCyclePacking
public import Oberwolfach.OrdinaryFactorGraphs

@[expose] public section

/-! An exact cycle factor for an almost-regular graph above the ordinary
cycle-decomposition threshold. The positive fractional cycle weights and the
local absorber/factor argument are proved dependencies, not supplied oracles.
This does not assert a factor theorem from minimum degree alone. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
set_option synthInstance.maxSize 512
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem ordinaryLocalPotential_full_domain {V:Type} [Fintype V] [DecidableEq V]
    {r:ℕ} (P:SimpleGraph V) (weight:OrdinaryCycle P r→ℝ) (D:ℝ) (v:V):
    ordinaryLocalPotential P P ⊥ Finset.univ (fun C=>2*weight C/D) v=
      ordinaryLocalTarget P ⊥ weight D v:=by
  unfold ordinaryLocalPotential ordinaryLocalTarget
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  have hC:C.val.val≤P:=C.property
  simp only [hC,SimpleGraph.bot_adj,false_implies,not_false_eq_true,implies_true,
    Finset.mem_univ,and_true]
  split_ifs <;> ring

theorem almost_regular_cycle_factor (m:ℕ) (hm:2≤m) (α:ℝ) (hα:0<α):
    ∃ ε:ℝ,0<ε ∧ ∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
    ∀ (P:SimpleGraph V) (D:ℝ),(Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
      (∀ v,(cycleThreshold (m+1)+α)*Fintype.card V≤(P.degree v:ℝ)) →
      (∀ v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V) →
      (m+1)∣Fintype.card V →
      HasResourceDecomposition (ordinaryCycleVertices P (m+1)) Finset.univ:=by
  obtain ⟨c,B,hc,hB,Nw,_hNw,hweights⟩:=positive_ordinary_fractional_cycle_weights (m+1) (by omega) α hα
  obtain ⟨ε₀,η,hε₀,hη,Nf,hfactor⟩:=ordinary_local_factor_from_fixed_weights m hm α 1 c B hα (by norm_num) le_rfl hc hB.le
  refine ⟨η/4,by positivity,max Nw Nf,?_⟩
  intro V _ _ hn P D hD hDup hP hreg hdiv
  obtain ⟨weight,hw,he⟩:=hweights V (by omega) P hP
  have he':=ordinary_cycle_incidence_load_adjacency P (m+1) weight he
  have hw' (C:OrdinaryCycle P (m+1)):
      c/(Fintype.card V:ℝ)^(m-1)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^(m-1):=by
    simpa only [show m+1-2=m-1 by omega] using hw C
  have hpb:(P\⊥)=P:=by ext a b;simp
  have hd:=hfactor V (by omega) P P ⊥ Finset.univ 0 1 1 0 D (η/4) 0 0
    le_rfl (by omega) le_rfl le_rfl le_rfl le_rfl hε₀.le (by positivity) le_rfl
    (by positivity) hD hDup hP hreg (by intro v;simp) (by
      intro S _
      simp only [one_pow,mul_one,one_mul,hpb,zero_mul,sub_zero]
      convert (le_rfl: ((common Finset.univ S (fun x=>P.neighborFinset x)).card:ℝ)≤
        (common Finset.univ S (fun x=>P.neighborFinset x)).card) using 1 <;> congr!)
    (by simpa only [Finset.card_univ] using hdiv) weight hw' he' (by
      intro v
      have hh:=ordinaryLocalPotential_full_domain P weight D v
      simpa only [one_pow,mul_one,mul_zero,sub_self,abs_zero] using (show
        |ordinaryLocalPotential P P ⊥ Finset.univ (fun C=>2*weight C/D) v-
          ordinaryLocalTarget P ⊥ weight D v|≤0 by rw [hh];simp))
    (by simp only [mul_zero,zero_div,add_zero];linarith only [hη])
  exact resource_decomposition_map localOrdinaryVertices (ordinaryCycleVertices P (m+1))
    (fun C:LocalOrdinaryCycle P ⊥ Finset.univ (m+1)=>C.val) (fun C=>rfl) Finset.univ hd

theorem ordinary_factor_graph_regular {V:Type} [Fintype V] [DecidableEq V]
    {P:SimpleGraph V} {r:ℕ} (M:Finset (OrdinaryCycle P r))
    (hdis:∀ C∈M,∀ D∈M,C≠D→Disjoint (ordinaryCycleVertices P r C) (ordinaryCycleVertices P r D))
    (hcover:M.biUnion (ordinaryCycleVertices P r)=Finset.univ):
    (ordinaryFactorGraph M).IsRegularOfDegree 2:=by
  intro v
  have hv:v∈M.biUnion (ordinaryCycleVertices P r):=by rw [hcover];exact Finset.mem_univ _
  obtain ⟨C,hC,hv⟩:=Finset.mem_biUnion.mp hv
  have hv':v∈C.val.val.support:=by simpa only [ordinaryCycleVertices,Set.mem_toFinset] using hv
  have hc:C.val.val.degree v=2:=by
    rcases C.val.property.degree_zero_or_two v with hz|ht
    · exact ((C.val.val.degree_eq_zero_iff_notMem_support v).mp hz hv').elim
    · exact ht
  have hle:C.val.val≤ordinaryFactorGraph M:=le_iSup_of_le C (le_iSup_of_le hC le_rfl)
  have hlo:=SimpleGraph.degree_le_of_le hle (v:=v)
  have hhi:=ordinaryFactorGraph_degree_le_two M hdis v
  omega

theorem regular_cycle_factor (m:ℕ) (hm:2≤m) (α:ℝ) (hα:0<α):
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
    ∀ (P:SimpleGraph V) (D:ℕ),P.IsRegularOfDegree D →
      (cycleThreshold (m+1)+α)*Fintype.card V≤(D:ℝ) →
      (m+1)∣Fintype.card V →
      ∃ M:Finset (OrdinaryCycle P (m+1)),
        (∀ C∈M,∀ E∈M,C≠E→Disjoint (ordinaryCycleVertices P (m+1) C) (ordinaryCycleVertices P (m+1) E)) ∧
        M.biUnion (ordinaryCycleVertices P (m+1))=Finset.univ ∧
        ordinaryFactorGraph M≤P ∧ (ordinaryFactorGraph M).IsRegularOfDegree 2:=by
  obtain ⟨ε,hε,N,hfactor⟩:=almost_regular_cycle_factor m hm α hα
  refine ⟨max N 1,?_⟩
  intro V _ _ hn P D hreg hD hdiv
  have hnpos:0<Fintype.card V:=by omega
  have hnR:(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hnpos
  obtain ⟨v⟩:=Fintype.card_pos_iff.mp hnpos
  have hhalf:(1/2:ℝ)≤cycleThreshold (m+1):=cycleThreshold_half_le (by omega)
  have hDlo:(Fintype.card V:ℝ)/2≤D:=by
    have hh:=mul_le_mul_of_nonneg_right hhalf hnR.le
    nlinarith only [hh,hD,mul_pos hα hnR]
  have hDhi:(D:ℝ)≤2*Fintype.card V:=by
    have hh:D<Fintype.card V:=by simpa only [hreg v] using P.degree_lt_card_verts v
    have hh':(D:ℝ)<Fintype.card V:=Nat.cast_lt.mpr hh
    linarith only [hh',hnR]
  obtain ⟨M,hM,hcover⟩:=hfactor V (by omega) P D hDlo hDhi
    (by intro w;simpa only [hreg w] using hD)
    (by intro w;simp only [hreg w,sub_self,abs_zero];positivity) hdiv
  exact ⟨M,hM,hcover,ordinaryFactorGraph_subhost M,ordinary_factor_graph_regular M hM hcover⟩

end Oberwolfach
