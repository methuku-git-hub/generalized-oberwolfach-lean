module

public import Oberwolfach.EdgeRetention
public import Oberwolfach.OrdinaryCycleIncidence

@[expose] public section

/-! A supplied vector near one is encoded by fixed independent physical
edge-retention probabilities. Absent edges are irrelevant to the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryRetentionProbability {V : Type*} (G : SimpleGraph V)
    (w : G.edgeSet → ℝ) (κ : ℝ) (e : Sym2 V) : ℝ :=
  if he : e∈G.edgeSet then w ⟨e,he⟩/(1+κ) else 1

theorem edge_vector_bounds {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : G.edgeSet → ℝ) (κ : ℝ)
    (hw : ‖w-(fun _ => (1:ℝ))‖≤κ) (e : G.edgeSet) :
    1-κ≤w e ∧ w e≤1+κ := by
  have hh := (norm_le_pi_norm (w-(fun _ => (1:ℝ))) e).trans hw
  change |w e-1|≤κ at hh
  exact ⟨by linarith [(abs_le.mp hh).1],by linarith [(abs_le.mp hh).2]⟩

theorem ordinary_retention_probability_bounds {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : G.edgeSet → ℝ) (κ : ℝ)
    (hκ : 0≤κ) (hκ1 : κ≤1) (hw : ‖w-(fun _ => (1:ℝ))‖≤κ) (e : Sym2 V) :
    0≤ordinaryRetentionProbability G w κ e ∧
      ordinaryRetentionProbability G w κ e≤1 ∧
      1-2*κ≤ordinaryRetentionProbability G w κ e := by
  have hd : 0<1+κ := by linarith
  unfold ordinaryRetentionProbability
  split_ifs with he
  · have hb := edge_vector_bounds G w κ hw ⟨e,he⟩
    refine ⟨div_nonneg (by linarith [hb.1]) hd.le,?_,?_⟩
    · apply (div_le_one hd).mpr
      exact hb.2
    · apply (le_div_iff₀ hd).mpr
      nlinarith [sq_nonneg κ]
  · constructor
    · norm_num
    · exact ⟨le_refl _,by linarith⟩

def ordinaryRetentionLaw {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : G.edgeSet → ℝ) (κ : ℝ)
    (hκ : 0≤κ) (hκ1 : κ≤1) (hw : ‖w-(fun _ => (1:ℝ))‖≤κ)
    (e : Sym2 V) : FiniteLaw Bool :=
  FiniteLaw.retentionCoin (ordinaryRetentionProbability G w κ e)
    (ordinary_retention_probability_bounds G w κ hκ hκ1 hw e).1
    (ordinary_retention_probability_bounds G w κ hκ hκ1 hw e).2.1

theorem ordinaryRetentionLaw_mass {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : G.edgeSet → ℝ) (κ : ℝ)
    (hκ : 0≤κ) (hκ1 : κ≤1) (hw : ‖w-(fun _ => (1:ℝ))‖≤κ)
    (e : Sym2 V) :
    (ordinaryRetentionLaw G w κ hκ hκ1 hw e).mass true=ordinaryRetentionProbability G w κ e := rfl

theorem ordinaryRetentionLaw_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : G.edgeSet → ℝ) (κ α : ℝ)
    (hκ : 0≤κ) (hκ1 : κ≤1) (hκα : κ≤α/16)
    (hw : ‖w-(fun _ => (1:ℝ))‖≤κ) (e : Sym2 V) :
    1-α/8≤(ordinaryRetentionLaw G w κ hκ hκ1 hw e).mass true := by
  rw [ordinaryRetentionLaw_mass]
  have hh := (ordinary_retention_probability_bounds G w κ hκ hκ1 hw e).2.2
  linarith

end Oberwolfach
