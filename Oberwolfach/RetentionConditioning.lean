module

public import Oberwolfach.AbsentColourConditioning
public import Oberwolfach.ConditionedProductComparison

@[expose] public section

/-! Conditioning on retention at one vertex is coordinatewise. The event
being compared can be any event determined by one other colour's masks. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_conditionEvent_zero {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (A : Ω → Prop) (hA : μ.probability A=0) :
    μ.conditionEvent A=μ := by
  simp only [FiniteLaw.conditionEvent,FiniteLaw.conditionOnMap,
    finiteLaw_boolean_event_mass,hA,dite_true]

theorem conditioned_absent_colourMask_l1_le {C : Type*} [Fintype C]
    (μ : FiniteLaw (C×Bool)) (A : C×Bool → Prop)
    (c : C) (habs : ∀ x,A x → x.1≠c) :
    ((μ.conditionEvent A).map (colourMask c)).l1Distance (μ.map (colourMask c))≤
      2*μ.probability (fun x=>x.1=c) := by
  by_cases hp : 0<μ.probability A
  · exact (conditioned_absent_colourMask_l1 μ A hp c habs).le
  · have hz : μ.probability A=0 := le_antisymm (le_of_not_gt hp) (finiteLaw_probability_nonneg _ _)
    rw [finiteLaw_conditionEvent_zero μ A hz]
    simp only [FiniteLaw.l1Distance,sub_self,abs_zero,Finset.sum_const_zero]
    exact mul_nonneg (by norm_num) (finiteLaw_probability_nonneg _ _)

def retentionCoordinateEvent {V C : Type*} (G : SimpleGraph V) (v : V) (b : C)
    (u : V) (x : C×Bool) : Prop :=
  if u=v then x.1=b ∧ x.2=true else if G.Adj v u then x.1≠b else True

theorem retentionCoordinateEvent_iff {V C : Type*}
    (G : SimpleGraph V) (v : V) (b : C) (σ : V → C×Bool) :
    (∀ u,retentionCoordinateEvent G v b u (σ u)) ↔ coinRetainedColour G σ v=some b := by
  rw [coinRetainedColour_eq_some]
  constructor
  · intro h
    obtain ⟨hc,hcoin⟩ : (σ v).1=b ∧ (σ v).2=true := by
      simpa only [retentionCoordinateEvent,ite_true] using h v
    refine ⟨hc,hcoin,?_⟩
    intro u hu
    have huv : u≠v := fun he=>G.irrefl (he ▸ hu)
    simpa only [retentionCoordinateEvent,huv,ite_false,hu,ite_true,hc] using h u
  · rintro ⟨hc,hcoin,hkeep⟩ u
    by_cases huv : u=v
    · subst u
      simp only [retentionCoordinateEvent,ite_true,hc,hcoin,and_self]
    · by_cases hu : G.Adj v u
      · simpa only [retentionCoordinateEvent,huv,ite_false,hu,ite_true,hc] using hkeep u hu
      · simp only [retentionCoordinateEvent,huv,hu,ite_false]

theorem retained_other_colour_covariance
    {V C : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (L : V → Finset C) (hL : ∀ u,(L u).Nonempty)
    (a : V → C → ℝ) (ha : ∀ u c,0≤a u c ∧ a u c≤1)
    {l : ℕ} (hl : 1<l) (hcard : ∀ u,(L u).card=l)
    (v : V) (b c : C) (hcb : c≠b) (B : (V → Option Bool) → Prop) :
    let μ := FiniteLaw.pi (fun u=>(FiniteLaw.uniformOn (L u) (hL u)).withCoin (a u) (ha u))
    |μ.probability (fun σ=>coinRetainedColour G σ v=some b ∧ B (fun u=>colourMask c (σ u)))-
      μ.probability (fun σ=>coinRetainedColour G σ v=some b)*
        μ.probability (fun σ=>B (fun u=>colourMask c (σ u)))|≤
      μ.probability (fun σ=>coinRetainedColour G σ v=some b)*
        (2/(l : ℝ)+2*(colourNeighbourSet G L v b).card/((l : ℝ)*((l : ℝ)-1))) := by
  classical
  dsimp only
  let μ := fun u=>(FiniteLaw.uniformOn (L u) (hL u)).withCoin (a u) (ha u)
  let A := retentionCoordinateEvent G v b
  let d := fun u=>((μ u).conditionEvent (A u) |>.map (colourMask c)).l1Distance
    ((μ u).map (colourMask c))
  let N := colourNeighbourSet G L v b
  have hlr : (1 : ℝ)<l := by exact_mod_cast hl
  have hl0 : (0 : ℝ)<l := by linarith
  have hden : 0<(l : ℝ)*((l : ℝ)-1) := mul_pos hl0 (by linarith)
  have hpoint (u : V) : d u≤(if u=v then 2/(l : ℝ) else 0)+
      (if u∈N then 2/((l : ℝ)*((l : ℝ)-1)) else 0) := by
    by_cases huv : u=v
    · subst u
      have hn : v∉N := by simp [N,colourNeighbourSet]
      simp only [ite_true,hn,ite_false,add_zero]
      have he : (μ v).conditionEvent (A v)=(μ v).conditionEvent (fun x=>x.1=b ∧ x.2=true) := by
        apply finiteLaw_conditionEvent_congr
        intro x
        simp [A,retentionCoordinateEvent]
      change ((μ v).conditionEvent (A v) |>.map (colourMask c)).l1Distance _≤_
      rw [he]
      have hh := conditioned_absent_colourMask_l1_le (μ v) (fun x=>x.1=b ∧ x.2=true) c
        (fun x hx hc=>hcb (hc.symm.trans hx.1))
      exact hh.trans (by
        have hp : (μ v).probability (fun x=>x.1=c)≤1/(l : ℝ) :=
          uniformOn_withCoin_colour_le (L v) (hL v) (a v) (ha v) (hcard v) c
        calc
          2*(μ v).probability (fun x=>x.1=c) ≤ 2*(1/(l : ℝ)) :=
            mul_le_mul_of_nonneg_left hp (by norm_num)
          _ = _ := by ring)
    · simp only [huv,ite_false,zero_add]
      by_cases hadj : G.Adj v u
      · have he : (μ u).conditionEvent (A u)=(μ u).conditionEvent (fun x=>x.1≠b) := by
          apply finiteLaw_conditionEvent_congr
          intro x
          simp [A,retentionCoordinateEvent,huv,hadj]
        change ((μ u).conditionEvent (A u) |>.map (colourMask c)).l1Distance _≤_
        rw [he]
        have hh := uniformOn_conditioned_colourMask_l1 (L u) (hL u) (a u) (ha u)
          hl (hcard u) b c hcb
        simpa only [N,colourNeighbourSet,Finset.mem_filter,Finset.mem_univ,true_and,hadj] using hh
      · have he : (μ u).conditionEvent (A u)=μ u := by
          calc
            _ = (μ u).conditionEvent (fun _=>True) := by
              apply finiteLaw_conditionEvent_congr
              intro x
              simp [A,retentionCoordinateEvent,huv,hadj]
            _ = _ := finiteLaw_conditionEvent_true _
        have hn : u∉N := by simp [N,colourNeighbourSet,hadj]
        change ((μ u).conditionEvent (A u) |>.map (colourMask c)).l1Distance _≤_
        rw [he]
        simp only [FiniteLaw.l1Distance,sub_self,abs_zero,Finset.sum_const_zero,hn,ite_false]
        exact le_refl _
  have hsum : (∑ u,d u)≤2/(l : ℝ)+2*(N.card : ℝ)/((l : ℝ)*((l : ℝ)-1)) := by
    apply (Finset.sum_le_sum (fun u _=>hpoint u)).trans_eq
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_ite_mem,Finset.univ_inter,
      Finset.sum_const,nsmul_eq_mul]
    ring
  have hh := finiteLaw_conditioned_map_covariance μ A (fun _=>colourMask c) B
  have he (σ : V → C×Bool) := retentionCoordinateEvent_iff G v b σ
  have hprob : (FiniteLaw.pi μ).probability (fun σ=>∀ u,A u (σ u))=
      (FiniteLaw.pi μ).probability (fun σ=>coinRetainedColour G σ v=some b) :=
    finiteLaw_probability_congr _ _ _ he
  have hprobB : (FiniteLaw.pi μ).probability (fun σ=>(∀ u,A u (σ u)) ∧ B (fun u=>colourMask c (σ u)))=
      (FiniteLaw.pi μ).probability (fun σ=>coinRetainedColour G σ v=some b ∧ B (fun u=>colourMask c (σ u))) := by
    apply finiteLaw_probability_congr
    intro σ
    exact and_congr_left' (he σ)
  rw [hprob,hprobB] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hsum (finiteLaw_probability_nonneg _ _))

end Oberwolfach
