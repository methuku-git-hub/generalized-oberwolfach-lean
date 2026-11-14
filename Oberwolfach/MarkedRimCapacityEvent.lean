module

public import Oberwolfach.MarkedRimReferenceDegrees
public import Oberwolfach.MarkedRimReferencePaths
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! One common physical event gives the marked reference degrees and the
ordinary two-step lower bound, with a uniform exponential error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [LinearOrder V]

theorem markedPhysicalRim_capacity_event
    (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (D ε δP γ pstar : ℝ) (hε : 0≤ε) (hδ : 0≤δP) (hδε : δP≤ε/4)
    (hγ : 0≤γ) (hpstar : 0≤pstar) (hlo : pstar≤p) (hn : 1≤Fintype.card V)
    (hPreg : ∀ x,|(P.degree x:ℝ)-D|≤δP*Fintype.card V)
    (hP : ∀ x,(1/2+γ)*Fintype.card V≤(P.degree x:ℝ))
    (hmaskD : 2*(b:ℝ)+1≤ε*Fintype.card V/4)
    (hmaskP : 2*(2*(b:ℝ)+1)≤γ*pstar^2*Fintype.card V/4) :
    1-20*(Fintype.card V:ℝ)^2*Real.exp (-min (ε^2/2) (γ^2*pstar^4/16)*Fintype.card V)≤
    (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
      (fun σ=>(∀ a x,
        |((∑ y,markedPhysicalRim P π b σ a x y:ℕ):ℝ)-(if a then k else p)*D|≤ε*Fintype.card V ∧
        |((∑ y,markedPhysicalRim P π b σ a y x:ℕ):ℝ)-(if a then k else p)*D|≤ε*Fintype.card V) ∧
        ∀ x y,x≠y →3/2*γ*p^2*Fintype.card V≤
        ((Finset.univ.filter (fun z=>0<markedPhysicalRim P π b σ false x z ∧
          0<markedPhysicalRim P π b σ false z y)).card:ℝ)) := by
  let n : ℝ := Fintype.card V
  have hn1 : 1≤n := by dsimp [n];exact_mod_cast hn
  have hn0 : 0<n := by linarith
  have hdeg := markedPhysicalRim_reference_degrees P π b p k hp hk hsum D ε δP hε hδ hδε hPreg hmaskD
  have hpath := markedPhysicalRim_reference_paths P π b p k hp hk hsum γ pstar hγ hpstar hlo hP hmaskP
  let μ := FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)
  have hjoint := finiteLaw_good_intersection μ
    (fun σ=>∀ a x,
      |((∑ y,markedPhysicalRim P π b σ a x y:ℕ):ℝ)-(if a then k else p)*D|≤ε*Fintype.card V ∧
      |((∑ y,markedPhysicalRim P π b σ a y x:ℕ):ℝ)-(if a then k else p)*D|≤ε*Fintype.card V)
    _ (2*n^2*Real.exp (-(γ*pstar^2*n/4)^2/n)) hpath
  have hbase := (sub_le_sub_right hdeg (2*n^2*Real.exp (-(γ*pstar^2*n/4)^2/n))).trans hjoint
  have heD : -2*(ε*n/2)^2/n=-(ε^2/2)*n := by field_simp [ne_of_gt hn0] <;> ring
  have heP : -(γ*pstar^2*n/4)^2/n=-(γ^2*pstar^4/16)*n := by field_simp [ne_of_gt hn0] <;> ring
  let c := min (ε^2/2) (γ^2*pstar^4/16)
  have heD' : Real.exp (-(ε^2/2)*n)≤Real.exp (-c*n) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (min_le_left (ε^2/2) (γ^2*pstar^4/16)) hn0.le
    linarith only [h]
  have heP' : Real.exp (-(γ^2*pstar^4/16)*n)≤Real.exp (-c*n) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (min_le_right (ε^2/2) (γ^2*pstar^4/16)) hn0.le
    linarith only [h]
  have hbD : 18*n*Real.exp (-2*(ε*n/2)^2/n)≤18*n^2*Real.exp (-c*n) := by
    rw [heD]
    apply mul_le_mul _ heD' (by positivity) (by positivity)
    nlinarith only [hn1]
  have hbP : 2*n^2*Real.exp (-(γ*pstar^2*n/4)^2/n)≤2*n^2*Real.exp (-c*n) := by
    rw [heP]
    exact mul_le_mul_of_nonneg_left heP' (by positivity)
  apply le_trans _ hbase
  change 1-20*n^2*Real.exp (-c*n)≤_
  change 1-20*n^2*Real.exp (-c*n)≤
    (1-18*n*Real.exp (-2*(ε*n/2)^2/n))-2*n^2*Real.exp (-(γ*pstar^2*n/4)^2/n)
  linarith only [hbD,hbP]

end Oberwolfach
