module

public import Oberwolfach.TransferConfigurationCounts
public import Oberwolfach.OrdinaryWheelResources
public import Oberwolfach.IndependentPatternSums

@[expose] public section

/-! Physical-edge survival of an ordinary transfer. The edge set is the
union of the constituent cycle edge sets, so a shared edge is tested once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {hr : 3 ≤ r} {P F : SimpleGraph V} {H : V → U → Prop} {v : V} {u u' : U}

def transferRequiredEdges (T : OrdinaryTransferConfiguration hr P F H v u u') : Finset (Sym2 V) :=
  Finset.univ.biUnion (fun j : TransferCycleIndex r=>
    (transferCycleGraph (by omega) T.labels v T.omitted j).edgeFinset)

theorem transferRequiredEdges_card (T : OrdinaryTransferConfiguration hr P F H v u u') :
    (transferRequiredEdges T).card≤(1+2*r)*r := by
  have hh := (Finset.card_biUnion_le : (transferRequiredEdges T).card≤
    ∑ j : TransferCycleIndex r,(transferCycleGraph (by omega) T.labels v T.omitted j).edgeFinset.card)
  have hc (j : TransferCycleIndex r) := (transferCycleGraph_isCycle hr T.labels v T.omitted j).edgeFinset_card
  simp only [hc,Finset.sum_const,Finset.card_univ,Fintype.card_sum,Fintype.card_unique,
    Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,smul_eq_mul,Nat.mul_comm] at hh
  convert hh using 1
  · unfold transferRequiredEdges
    congr!
  · ring

theorem transferRequiredEdges_subset (T : OrdinaryTransferConfiguration hr P F H v u u') :
    transferRequiredEdges T⊆P.edgeFinset := by
  intro e he
  obtain ⟨j,_,he⟩ := Finset.mem_biUnion.mp he
  rw [SimpleGraph.mem_edgeFinset] at he ⊢
  exact SimpleGraph.edgeSet_mono (T.rim_edges j) he

theorem transferRequiredEdges_endpoints (T : OrdinaryTransferConfiguration hr P F H v u u')
    (x y : V) (he : s(x,y)∈transferRequiredEdges T) :
    x≠y ∧ x∈insert v (Set.range T.labels) ∧ y∈insert v (Set.range T.labels) := by
  obtain ⟨j,_,he⟩ := Finset.mem_biUnion.mp he
  rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at he
  refine ⟨he.ne,?_,?_⟩
  · exact transferCycleGraph_support_subset hr T.labels v T.omitted j ⟨y,he⟩
  · exact transferCycleGraph_support_subset hr T.labels v T.omitted j ⟨x,he.symm⟩

theorem transfer_configuration_total :
    (Fintype.card (OrdinaryTransferConfiguration hr P F H v u u'):ℝ)≤(Fintype.card V:ℝ)^(r^2) := by
  have hh := ordinary_transfer_configuration_root_count (hr:=hr) (Q:=P) (F:=F) (H:=H) (v:=v) (u:=u) (u':=u') ∅
  simpa only [Finset.coe_empty,Set.empty_subset,ite_true,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,mul_one,Finset.card_empty,pow_zero,one_mul,Nat.sub_zero] using hh

theorem transfer_required_edge_incidence (hn : 0<Fintype.card V) (e : Sym2 V) :
    (∑ T : OrdinaryTransferConfiguration hr P F H v u u',if e∈transferRequiredEdges T
      then 1/(Fintype.card V:ℝ)^(r^2) else 0)≤(r:ℝ)^2/Fintype.card V := by
  induction e using Sym2.ind with
  | _ x y=>
    by_cases hxy : x=y
    · have hnone : ∀ T : OrdinaryTransferConfiguration hr P F H v u u',s(x,y)∉transferRequiredEdges T :=
        fun T he=>(transferRequiredEdges_endpoints T x y he).1 hxy
      simp only [hnone,ite_false,Finset.sum_const_zero]
      positivity
    · let z := if x=v then y else x
      have hz : z≠v := by
        dsimp [z]
        split_ifs with hx
        · exact fun hy=>hxy (hx.trans hy.symm)
        · exact hx
      have hlabel (T : OrdinaryTransferConfiguration hr P F H v u u')
          (he : s(x,y)∈transferRequiredEdges T) : z∈Set.range T.labels := by
        have hh := transferRequiredEdges_endpoints T x y he
        have hs : z∈insert v (Set.range T.labels) := by
          dsimp [z]
          split_ifs
          · exact hh.2.2
          · exact hh.2.1
        exact (Set.mem_insert_iff.mp hs).resolve_left hz
      have hh := ordinary_transfer_configuration_root_count (hr:=hr) (Q:=P) (F:=F) (H:=H) (v:=v) (u:=u) (u':=u') {z}
      have hc : (∑ T : OrdinaryTransferConfiguration hr P F H v u u',if s(x,y)∈transferRequiredEdges T then (1:ℝ) else 0)≤
          (r:ℝ)^2*(Fintype.card V:ℝ)^(r^2-1) := by
        apply le_trans _ (by simpa only [Finset.card_singleton,pow_one] using hh)
        apply Finset.sum_le_sum
        intro T _
        by_cases he : s(x,y)∈transferRequiredEdges T
        · simp only [he,ite_true]
          have hs : (↑({z}:Finset V):Set V)⊆Set.range T.labels := by simpa using hlabel T he
          simp only [hs,ite_true,le_refl]
        · simp only [he,ite_false]
          split_ifs <;> norm_num
      have heq : (∑ T : OrdinaryTransferConfiguration hr P F H v u u',if s(x,y)∈transferRequiredEdges T
          then 1/(Fintype.card V:ℝ)^(r^2) else 0)=
          (∑ T : OrdinaryTransferConfiguration hr P F H v u u',if s(x,y)∈transferRequiredEdges T then (1:ℝ) else 0)/(Fintype.card V:ℝ)^(r^2) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro T _
        split_ifs <;> simp
      rw [heq]
      calc
        _ ≤ ((r:ℝ)^2*(Fintype.card V:ℝ)^(r^2-1))/(Fintype.card V:ℝ)^(r^2) :=
          div_le_div_of_nonneg_right hc (by positivity)
        _ = _ := by
          have he : r^2=(r^2-1)+1 := by
            have hp : 0<r^2 := by positivity
            omega
          nth_rw 2 [he]
          rw [pow_succ]
          have hn0 : (Fintype.card V:ℝ)≠0 := by positivity
          field_simp
          simp only [pow_succ]

end Oberwolfach
