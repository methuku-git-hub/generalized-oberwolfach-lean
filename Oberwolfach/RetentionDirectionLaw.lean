module

public import Oberwolfach.FiniteProductRegrouping
public import Oberwolfach.EdgeRetention
public import Oberwolfach.RandomColourCuts

@[expose] public section

/-! Retention of a physical edge and its independent fair direction have
exactly the two-colour direction law. The direction of an unretained edge
is still present in the experiment, for subsequent insertions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def retentionColourProbability (p : ℝ) (a : Fin 2) : ℝ := if a=0 then p else 1-p

theorem retentionColourProbability_nonneg (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (a : Fin 2) :
    0≤retentionColourProbability p a := by unfold retentionColourProbability;split_ifs <;> linarith

theorem retentionColourProbability_sum (p : ℝ) : ∑ a,retentionColourProbability p a=1 := by
  simp [Fin.sum_univ_two,retentionColourProbability]

def retentionDirectionToColour (z : Bool×Bool) : Fin 2×Bool := (if z.1 then 0 else 1,z.2)

theorem retentionDirection_map (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    ((FiniteLaw.retentionCoin p hp hp1).prod FiniteLaw.fairCoin).map retentionDirectionToColour=
      FiniteLaw.categoricalDirection (retentionColourProbability p)
        (retentionColourProbability_nonneg p hp hp1) (retentionColourProbability_sum p) := by
  apply finiteLaw_ext
  intro z
  rcases z with ⟨a,b⟩
  fin_cases a <;> cases b <;>
    simp [FiniteLaw.map,FiniteLaw.prod,FiniteLaw.retentionCoin,FiniteLaw.fairCoin,
      FiniteLaw.categoricalDirection,retentionDirectionToColour,retentionColourProbability,
      Fintype.sum_prod_type,Fintype.sum_bool] <;> ring

theorem retentionDirection_orientation
    {V : Type*} [LinearOrder V] (P : SimpleGraph V) (σ : Sym2 V→Bool×Bool) :
    sampledOrientation (retainedGraph P (fun e=>(σ e).1)) (fun e=>(σ e).2)=
      sampledColourOrientation P (fun e=>retentionDirectionToColour (σ e)) 0 := by
  funext x y
  cases h : (σ s(x,y)).1 <;>
    simp [sampledOrientation,retainedGraph,sampledColourOrientation,retentionDirectionToColour,
      Prod.ext_iff,h,and_assoc]

theorem retention_orientation_probability
    {V : Type*} [Fintype V] [LinearOrder V] (P : SimpleGraph V)
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (E : (V→V→ℕ)→Prop) :
    ((FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.retentionCoin p hp hp1)).prod
      (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.fairCoin))).probability
      (fun z=>E (sampledOrientation (retainedGraph P z.1) z.2))=
    (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.categoricalDirection (retentionColourProbability p)
      (retentionColourProbability_nonneg p hp hp1) (retentionColourProbability_sum p))).probability
      (fun σ=>E (sampledColourOrientation P σ 0)) := by
  rw [finiteLaw_pi_prod_probability
    (fun _ : Sym2 V=>FiniteLaw.retentionCoin p hp hp1)
    (fun _ : Sym2 V=>FiniteLaw.fairCoin)
    (fun c b=>E (sampledOrientation (retainedGraph P c) b))]
  have hh := finiteLaw_map_probability
    (FiniteLaw.pi (fun _ : Sym2 V=>(FiniteLaw.retentionCoin p hp hp1).prod FiniteLaw.fairCoin))
    (fun σ e=>retentionDirectionToColour (σ e)) (fun σ=>E (sampledColourOrientation P σ 0))
  rw [finiteLaw_pi_map] at hh
  simp only [retentionDirection_map] at hh
  rw [hh]
  congr 1
  funext σ
  rw [retentionDirection_orientation]

end Oberwolfach
