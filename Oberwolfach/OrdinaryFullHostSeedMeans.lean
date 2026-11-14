module

public import Oberwolfach.OrdinaryRawMeanFactors
public import Oberwolfach.OrdinarySeedLift
public import Oberwolfach.OrdinaryAdmissibleCycleLoads

@[expose] public section

/-! Expected loads of the manuscript's fixed full-host seed weighting,
including the exact normalization and explicit conflict-exclusion error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 150000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

def ordinaryFullHostSeed (P F : SimpleGraph V) (r : ℕ)
    (weight : OrdinaryCycle P r → ℝ) (pR pH : ℝ) :
    OrdinaryWheel P F (fun _ : V=>fun _ : U=>True) r → ℝ :=
  ordinaryCycleWheelWeight P F r weight ((Fintype.card U:ℝ)*pR^(r-1)*pH^r)

variable (P F : SimpleGraph V) (r : ℕ) (hr : 1≤r)
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (hF : permutationConflictGraph π (3*d)≤F)
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (pR pH : ℝ) (hpR : 0<pR) (hpR1 : pR≤1) (hpH : 0<pH)
    (hm : 0<Fintype.card U)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (j : Color) (hj : ∀ u,s u j=pH)
    (weight : OrdinaryCycle P r → ℝ)

local notation "μwheel" => rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>hpR.le) (fun _=>hpR1) d hd q hq hQ s hs hS
local notation "wseed" => ordinaryFullHostSeed (U:=U) P F r weight pR pH

attribute [local instance] Classical.propDecidable

include hr hF hnoshort hpH hm hj

theorem ordinaryFullHostSeed_rim_mean (x y : V) :
    (FiniteLaw.pi μwheel).expectation (fun σ=>
      ordinaryPotentialLoad wseed (Sum.inl s(x,y)) (rawWheelGraph P σ) (rawWheelSpokes π d σ j))=
      ∑ C,if C.val.val.Adj x y ∧ (∀ v∈C.val.val.support,∀ z∈C.val.val.support,¬F.Adj v z)
        then weight C else 0 := by
  have hh := ordinaryRawPotentialLoad_rim_mean P F (fun _ : V=>fun _ : U=>True) r hr π d hd hF hnoshort
    pR pH hpR hpR1 hpH q hq hQ s hs hS j hj wseed x y
  erw [hh]
  unfold ordinaryFullHostSeed
  rw [ordinaryCycleWheelWeight_rim_load]
  have hm0 : (Fintype.card U:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp [hm0,hpR.ne',hpH.ne'] <;> ring

theorem ordinaryFullHostSeed_spoke_mean (v : V) (u : U) :
    (FiniteLaw.pi μwheel).expectation (fun σ=>
      ordinaryPotentialLoad wseed (Sum.inr (v,u)) (rawWheelGraph P σ) (rawWheelSpokes π d σ j))=
      pR/((Fintype.card U:ℝ)*pH) *
        ∑ C,if v∈C.val.val.support ∧ (∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y)
          then weight C else 0 := by
  have hh := ordinaryRawPotentialLoad_spoke_mean P F (fun _ : V=>fun _ : U=>True) r hr π d hd hF hnoshort
    pR pH hpR hpR1 hpH q hq hQ s hs hS j hj wseed v u
  erw [hh]
  unfold ordinaryFullHostSeed
  rw [ordinaryCycleWheelWeight_spoke_load]
  have hm0 : (Fintype.card U:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hrpow : r-1+1=r := Nat.sub_add_cancel hr
  have hR : pR^r=pR*pR^(r-1) := by rw [← pow_succ',Nat.sub_add_cancel hr]
  have hH : pH^r=pH*pH^(r-1) := by rw [← pow_succ',Nat.sub_add_cancel hr]
  rw [hR,hH]
  field_simp [hm0,hpR.ne',hpH.ne'] <;> ring


theorem ordinaryFullHostSeed_rim_mean_error (hr2 : 2≤r) (hn : 0<Fintype.card V)
    (hweight : ∀ C,0≤weight C) (B : ℝ) (hB : 0≤B)
    (hb : ∀ C,weight C≤B/(Fintype.card V:ℝ)^(r-2))
    (L : ℝ) (hdeg : ∀ v,(F.degree v:ℝ)≤L)
    (he : ∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0)
    (x y : V) (hxy : P.Adj x y) (hFxy : ¬F.Adj x y) :
    |(FiniteLaw.pi μwheel).expectation (fun σ=>
      ordinaryPotentialLoad wseed (Sum.inl s(x,y)) (rawWheelGraph P σ) (rawWheelSpokes π d σ j))-1|≤
      5*(r:ℝ)^4*B*L/Fintype.card V := by
  rw [ordinaryFullHostSeed_rim_mean P F r hr π d hd hF hnoshort pR pH hpR hpR1 hpH hm
    q hq hQ s hs hS j hj weight x y]
  convert ordinary_admissible_cycle_edge_load P F r hr2 hn weight hweight B hB hb L hdeg he x y hxy hFxy using 1 <;> congr!

theorem ordinaryFullHostSeed_spoke_mean_error (hr2 : 2≤r) (hn : 0<Fintype.card V)
    (hweight : ∀ C,0≤weight C) (B : ℝ) (hB : 0≤B)
    (hb : ∀ C,weight C≤B/(Fintype.card V:ℝ)^(r-2))
    (L : ℝ) (hdeg : ∀ v,(F.degree v:ℝ)≤L)
    (he : ∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0)
    (D₀ : ℝ) (hD₀ : 0<D₀) (hbalance : pR*D₀=2*(Fintype.card U:ℝ)*pH)
    (v : V) (u : U) :
    |(FiniteLaw.pi μwheel).expectation (fun σ=>
      ordinaryPotentialLoad wseed (Sum.inr (v,u)) (rawWheelGraph P σ) (rawWheelSpokes π d σ j))-
        (P.degree v:ℝ)/D₀|≤6*(r:ℝ)^4*B*L/D₀ := by
  rw [ordinaryFullHostSeed_spoke_mean P F r hr π d hd hF hnoshort pR pH hpR hpR1 hpH hm
    q hq hQ s hs hS j hj weight v u]
  have hm0 : (0:ℝ)<Fintype.card U := by exact_mod_cast hm
  have hco : pR/((Fintype.card U:ℝ)*pH)=2/D₀ := by
    apply (div_eq_div_iff (by positivity) hD₀.ne').mpr
    nlinarith only [hbalance]
  rw [hco]
  let S : ℝ := ∑ C,if v∈C.val.val.support ∧ (∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y)
    then weight C else 0
  have hcycle : |S-(P.degree v:ℝ)/2|≤3*(r:ℝ)^4*B*L := by
    convert ordinary_admissible_cycle_vertex_load P F r hr2 hn weight hweight B hB hb L hdeg he v using 1 <;> congr!
  change |2/D₀*S-(P.degree v:ℝ)/D₀|≤_
  calc
    _ = (2/D₀)*|S-(P.degree v:ℝ)/2| := by
      have halg : 2/D₀*S-(P.degree v:ℝ)/D₀=(2/D₀)*(S-(P.degree v:ℝ)/2) := by ring
      rw [halg,abs_mul,abs_of_pos (div_pos (by norm_num) hD₀)]
    _ ≤ (2/D₀)*(3*(r:ℝ)^4*B*L) := mul_le_mul_of_nonneg_left hcycle (by positivity)
    _ = _ := by ring

end Oberwolfach
