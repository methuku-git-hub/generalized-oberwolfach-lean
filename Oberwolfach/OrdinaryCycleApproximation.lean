module

public import Oberwolfach.FractionalSampleBounds
public import Oberwolfach.SampledInducedEdges
public import Oberwolfach.SampledInducedFractional
public import Oberwolfach.OrdinaryRetentionLaw
public import Oberwolfach.OrdinaryCycleWeightRestriction

@[expose] public section

/-! Bounded approximate cycle weights for every supplied edge vector near one.
The error is the probability of an unsuccessful sample containing the edge,
normalized by its exact two-vertex inclusion probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_cycle_approximation_at_size (r : ℕ) (hr : 3≤r) (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ m≥N,4≤m → 3≤α*m/4 →
      ∀ (V : Type) [Fintype V] [DecidableEq V],m≤Fintype.card V →
      ∀ G : SimpleGraph V,
        (∀ v,(cycleThreshold r+α)*Fintype.card V≤(G.degree v:ℝ)) →
      ∀ κ : ℝ,0≤κ → κ≤1 → κ≤α/16 →
      ∀ w : G.edgeSet → ℝ,‖w-(fun _ => (1:ℝ))‖≤κ →
      ∃ a : OrdinaryCycle G r → ℝ,
        (∀ C,0≤a C ∧ a C≤4*(m:ℝ)^(r-2)/(Fintype.card V:ℝ)^(r-2)) ∧
        ‖(∑ C,a C • ordinaryCycleIncidence G r C)-w‖≤
          8*m*Real.exp (-α^2*m/32) := by
  obtain ⟨N,hN⟩ := sampled_induced_fractional r hr α hα
  refine ⟨N,?_⟩
  intro m hm hm4 hroots V _ _ hmn G hdeg κ hκ hκ1 hκα w hw
  letI : Nonempty (FixedSubset V m) := fixedSubset_nonempty hmn
  let μ := ordinaryRetentionLaw G w κ hκ hκ1 hw
  let ν := (FiniteLaw.uniform (FixedSubset V m)).prod (FiniteLaw.pi μ)
  let J := sampledInducedGraph (m:=m) G
  let good := sampledInducedDense (m:=m) G (cycleThreshold r) α
  let ρ := pairSampleProbability (Fintype.card V) m
  let t := ρ/(1+κ)
  have hρ : 0<ρ := pairSampleProbability_pos (by omega) hmn
  have hκ' : 0<1+κ := by linarith
  have ht : 0<t := div_pos hρ hκ'
  have hsub (z : FixedSubset V m × (Sym2 V → Bool)) : J z≤G :=
    (spanningRestriction_le _ _).trans (retainedGraph_le _ _)
  have hsupp (z : FixedSubset V m × (Sym2 V → Bool)) : (J z).support⊆z.1.val :=
    spanningRestriction_support _ _
  obtain ⟨a,ha,hs,hb,he,hloss⟩ := fractional_cycle_sample_average_bounded hmn ν Prod.fst
    (finiteLaw_prod_map_fst _ _) G J good hsub hsupp (fun z hz => hN V m hm G z hz) t ht
  refine ⟨fun C => a C.val.val,?_,?_⟩
  · intro C
    exact ⟨ha _,(hb _ C.val.property).trans (cycle_sample_coefficient_scale
      (by omega) hmn (by omega) κ hκ hκ1)⟩
  · apply (pi_norm_le_iff_of_nonneg (show 0≤8*(m:ℝ)*Real.exp (-α^2*m/32) by positivity)).mpr
    intro e
    rw [Pi.sub_apply,Finset.sum_apply]
    simp only [Pi.smul_apply,smul_eq_mul,Real.norm_eq_abs]
    rw [ordinaryCycle_load_from_graph_weights G r a ha hs e]
    rcases e with ⟨e,heG⟩
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := heG
      have hpair : (({u,v}:Finset V).card)=2 := by simp [huv.ne]
      have hfull : ν.probability (fun z => (J z).Adj u v)/t=w ⟨s(u,v),heG⟩ := by
        rw [sampledInducedGraph_edge_probability hmn G μ u v huv]
        change ρ*ordinaryRetentionProbability G w κ s(u,v)/(ρ/(1+κ))=_
        rw [ordinaryRetentionProbability,dif_pos heG]
        field_simp
      have hbad : ν.probability (fun z => ¬good z ∧ (J z).Adj u v)≤
          4*m*Real.exp (-α^2*m/32)*ρ := by
        calc
          _ ≤ ν.probability (fun z => ({u,v}:Finset V)⊆z.1.val ∧ ¬good z) := by
            apply finiteLaw_probability_mono
            intro z hz
            have hz' := (spanningRestriction_adj _ _ _ _).mp hz.2
            exact ⟨by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using ⟨hz'.2.1,hz'.2.2⟩,hz.1⟩
          _ ≤ 4*m*Real.exp (-α^2*m/32)*
              (FiniteLaw.uniform (FixedSubset V m)).probability (fun S => ({u,v}:Finset V)⊆S.val) := by
            exact sampled_induced_dense_failure G {u,v} m hmn (by rw [hpair];omega) μ
              (cycleThreshold r) α hα hdeg (by rw [hpair];norm_num;exact hroots)
              (ordinaryRetentionLaw_lower G w κ α hκ hκ1 hκα hw)
          _ = _ := by
            congr 1
            simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using
              fixedSubset_pair_probability hmn u v huv.ne
      have hlower : 0≤ν.probability (fun z => ¬good z ∧ (J z).Adj u v)/t :=
        div_nonneg (finiteLaw_probability_nonneg _ _) ht.le
      have hupper : ν.probability (fun z => ¬good z ∧ (J z).Adj u v)/t≤
          8*m*Real.exp (-α^2*m/32) := by
        calc
          _ ≤ (4*m*Real.exp (-α^2*m/32)*ρ)/t := div_le_div_of_nonneg_right hbad ht.le
          _ = 4*m*Real.exp (-α^2*m/32)*(1+κ) := by dsimp [t];field_simp
          _ ≤ _ := by
            have hp : 0≤4*(m:ℝ)*Real.exp (-α^2*m/32) := by positivity
            have hh := mul_le_mul_of_nonneg_left hκ1 hp
            nlinarith only [hh]
      have hh := hloss u v
      rw [hfull] at hh
      simp only [SimpleGraph.mem_edgeSet]
      apply abs_le.mpr
      constructor <;> linarith

end Oberwolfach
