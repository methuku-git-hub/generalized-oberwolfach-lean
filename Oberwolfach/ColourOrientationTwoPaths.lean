module

public import Oberwolfach.ColouredTwoPaths
public import Oberwolfach.ColourDegreeEvent

@[expose] public section

/-! Concentration of directed two-step paths in one retained colour.
The two physical coordinates of distinct eligible paths are disjoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [LinearOrder V] {R : ℕ}

theorem sampledColourOrientation_twoPath_pattern
    (G : SimpleGraph V) (σ : Sym2 V→Fin R×Bool) (a : Fin R)
    {x y z : V} (hxy : x≠y) (hxz : G.Adj x z) (hzy : G.Adj z y) :
    patternValue (twoEdgeCoordinates x y z) (fun e=>(a,twoEdgeRequirements x y z e)) σ=
      if 0<sampledColourOrientation G σ a x z ∧ 0<sampledColourOrientation G σ a z y then 1 else 0 := by
  have he : s(z,y)≠s(x,z) := by simp only [ne_eq,Sym2.eq_iff];aesop
  simp only [patternValue_indicator,twoEdgeCoordinates,Finset.mem_insert,
    Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  simp only [twoEdgeRequirements,ite_eq_right he]
  by_cases h1 : σ s(x,z)=(a,orientationBit x z) <;>
    by_cases h2 : σ s(z,y)=(a,orientationBit z y) <;>
      simp [sampledColourOrientation,hxz,hzy,h1,h2]

theorem sampledColourOrientation_twoPath_patterns
    (G E : SimpleGraph V) (hEG : E≤G) (σ : Sym2 V→Fin R×Bool) (a : Fin R)
    {x y : V} (hxy : x≠y) :
    (eligibleTwoPathCount E (sampledColourOrientation G σ a) x y:ℝ)=
      ∑ z∈E.neighborFinset x∩E.neighborFinset y,
        patternValue (twoEdgeCoordinates x y z) (fun e=>(a,twoEdgeRequirements x y z e)) σ := by
  rw [eligibleTwoPathCount,Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hxz : E.Adj x z := by simpa using (Finset.mem_inter.mp hz).1
  have hyz : E.Adj y z := by simpa using (Finset.mem_inter.mp hz).2
  rw [sampledColourOrientation_twoPath_pattern G σ a hxy (hEG hxz) (hEG hyz.symm)]
  split_ifs <;> norm_num

theorem sampledColourOrientation_twoPath_tail
    (G E : SimpleGraph V) (hEG : E≤G)
    (ρ : Fin R→ℝ) (hρ : ∀ a,0≤ρ a) (hsum : ∑ a,ρ a=1) (a : Fin R)
    {x y : V} (hxy : x≠y) {t : ℝ} (ht : 0≤t) :
    (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum)).probability
      (fun σ=>t≤|(eligibleTwoPathCount E (sampledColourOrientation G σ a) x y:ℝ)-
        ((E.neighborFinset x∩E.neighborFinset y).card:ℝ)*(ρ a/2)^2|)≤
      2*Real.exp (-t^2/Fintype.card V) := by
  let C := E.neighborFinset x∩E.neighborFinset y
  have hh := finiteLaw_fixed_size_patterns_tail_at_scale
    (fun _ : Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum) C (twoEdgeCoordinates x y)
    (fun z e=>(a,twoEdgeRequirements x y z e)) 2 (by omega)
    (fun _ _=>twoEdgeCoordinates_card hxy)
    (common_two_path_edges_disjoint E x y hxy)
    (n:=(Fintype.card V:ℝ)) (by exact_mod_cast Finset.card_le_univ C) ht
  have he (z : V) : s(x,z)≠s(z,y) := by
    intro h;rcases Sym2.eq_iff.mp h with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> exact hxy (by aesop)
  have hmass (z : V) :
      (∏ e∈twoEdgeCoordinates x y z,(FiniteLaw.categoricalDirection ρ hρ hsum).mass
        (a,twoEdgeRequirements x y z e))=(ρ a/2)^2 := by
    simp only [twoEdgeCoordinates,Finset.prod_insert,Finset.mem_singleton,he z,not_false_eq_true,Finset.prod_singleton]
    simp [FiniteLaw.categoricalDirection,pow_two]
  simp only [hmass,Finset.sum_const,nsmul_eq_mul] at hh
  simpa only [C,← sampledColourOrientation_twoPath_patterns G E hEG _ a hxy,
    Nat.cast_ofNat,show -2*t^2/((Fintype.card V:ℝ)*2)=-t^2/Fintype.card V by ring] using hh

end Oberwolfach
