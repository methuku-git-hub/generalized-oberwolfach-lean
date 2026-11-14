module

public import Oberwolfach.MarkedSampleSeedLoadIdentities
public import Oberwolfach.RawMarkedPotentialSampling
public import Oberwolfach.MarkedSampleCycleValidity
public import Oberwolfach.SuccessorSeedBounds

@[expose] public section

/-! Construct the actual wheel coefficients required for approximate packing
from the fixed parent weights and typed potential-load estimates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sample_seed_witness
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:1≤m) (hn:0<Fintype.card V)
    (D τ A B p k s₀ pstar η:ℝ)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀)
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀≤1) (hA:0≤A) (hB:0≤B) (hη:0≤η)
    (weight:(Fin (m+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (hq:∀ u,0<q u g) (hS:∀ u,0<s u j)
    (hload:
      let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
      ∀ root,rawMarkedWheelMarginal P π d p k q s g j root≠0→
        |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-1|≤η):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let ψ:=fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true)=>weight W.1.val/(D*p^m*k*s₀^m)
    (∀ e,|markedWheelRimLoad ψ e-1|≤η)∧
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η)∧
    (∀ W,(A/2)/(Fintype.card V:ℝ)^m≤ψ W∧ψ W≤(2*B/pstar^(2*m+1))/(Fintype.card V:ℝ)^m):=by
  intro E K ψ
  refine ⟨?_,?_,?_⟩
  · intro e
    rw [←marked_sample_seed_rim_load P π d m D p k s₀ weight σ H e]
    apply hload
    cases e with
    | inl e=>
      have he:=(markedPhysicalRim_eq_one_iff P π (3*d) _ false e.val.1 e.val.2).mp e.property
      have he' : ¬PermutationClose π (3*d) e.val.1 e.val.2 ∧ P.Adj e.val.1 e.val.2 := ⟨he.1,he.2.1⟩
      simpa only [Sum.map_inl,rawMarkedWheelMarginal,if_pos he'] using (hpstar.trans_le hp).ne'
    | inr e=>
      have he:=(markedPhysicalRim_eq_one_iff P π (3*d) _ true e.val.1 e.val.2).mp e.property
      have he' : ¬PermutationClose π (3*d) e.val.1 e.val.2 ∧ P.Adj e.val.1 (π e.val.2) := ⟨he.1,he.2.1⟩
      simpa only [Sum.map_inr,rawMarkedWheelMarginal,if_pos he'] using (hpstar.trans_le hk).ne'
  · intro mark v u
    by_cases he:if mark then H true v u else H false v u
    · have he':H mark v u:=by cases mark <;> exact he
      rw [markedSpokeResidual,if_pos he,abs_sub_comm,
        ←marked_sample_seed_spoke_load P π d m D p k s₀ weight σ H mark v u he']
      apply hload
      cases mark <;> simp only [rawMarkedWheelMarginal,Bool.false_eq_true,ite_false,ite_true]
      · exact (hS u).ne'
      · exact (hq u).ne'
    · rw [markedSpokeResidual_outside ψ mark v u he,abs_zero]
      exact hη
  · intro W
    exact ⟨successor_seed_positive_lower hw hm hn hDlo hDhi p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hA hB
      W.1.val (marked_sample_cycle_valid P π (3*d) m _ W.1) W.1.property.1,
      (successor_seed_nonneg_upper hw hm hn hDlo hDhi p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB W.1.val).2⟩

end Oberwolfach
