module

public import Oberwolfach.CoordinateLocalLemma

@[expose] public section

/-! A numerical symmetric local lemma with a simple explicit degree bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_product_one_sub_lower
    {I : Type*} [DecidableEq I] (S : Finset I) (x : I → ℝ)
    (hx : ∀ i∈S,0≤x i ∧ x i≤1) :
    1-∑ i∈S,x i≤∏ i∈S,(1-x i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hxi := hx i (Finset.mem_insert_self _ _)
    have hxS := fun j hj=>hx j (Finset.mem_insert_of_mem hj)
    have hs0 : 0≤∑ j∈S,x j := Finset.sum_nonneg (fun j hj=>(hxS j hj).1)
    have hm := mul_le_mul_of_nonneg_left (ih hxS) (sub_nonneg.mpr hxi.2)
    rw [Finset.sum_insert hi,Finset.prod_insert hi]
    nlinarith [mul_nonneg hxi.1 hs0]

theorem finiteLaw_symmetric_localLemma
    {Ω I : Type*} [Fintype Ω] [DecidableEq I]
    (μ : FiniteLaw Ω) (A : I → Ω → Prop) (N : I → Finset I)
    {d : ℕ} (hd : 0<d) (hdeg : ∀ i,(N i).card≤d)
    (hind : ∀ i T,i∉T → Disjoint T (N i) →
      μ.probability (fun ω=>A i ω ∧ avoidsEvents A T ω)=
        μ.probability (A i)*μ.probability (avoidsEvents A T))
    (hp : ∀ i,μ.probability (A i)≤1/(4*(d : ℝ))) (S : Finset I) :
    0<μ.probability (avoidsEvents A S) := by
  let x : ℝ := 1/(2*(d : ℝ))
  have hdr : (1 : ℝ)≤d := by exact_mod_cast hd
  have hden : 0<2*(d : ℝ) := by positivity
  have hx0 : 0<x := one_div_pos.mpr hden
  have hxhalf : x≤1/2 := by
    change 1/(2*(d : ℝ))≤1/2
    apply (div_le_iff₀ hden).mpr
    linarith
  have hx1 : x<1 := by linarith
  apply finiteLaw_localLemma μ A N (fun _=>x) (fun _=>hx0.le) (fun _=>hx1) hind
  intro i
  have hprod := finite_product_one_sub_lower (N i) (fun _=>x) (fun _ _=>⟨hx0.le,hx1.le⟩)
  simp only [Finset.sum_const,nsmul_eq_mul] at hprod
  have hcard : ((N i).card : ℝ)≤d := by exact_mod_cast hdeg i
  have hmul : ((N i).card : ℝ)*x≤1/2 := by
    calc
      _ ≤ (d : ℝ)*x := mul_le_mul_of_nonneg_right hcard hx0.le
      _ = 1/2 := by dsimp [x];field_simp
  have hprodhalf : 1/2≤∏ j∈N i,(1-x) := by linarith
  have hidentity : x*(1/2)=1/(4*(d : ℝ)) := by dsimp [x];ring
  calc
    _ ≤ 1/(4*(d : ℝ)) := hp i
    _ = x*(1/2) := hidentity.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hprodhalf hx0.le

end Oberwolfach
