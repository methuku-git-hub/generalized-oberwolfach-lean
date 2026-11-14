module

public import Oberwolfach.OrdinaryBoundarySelectionMargins
public import Oberwolfach.OrdinaryBoundaryRootSets

@[expose] public section
/-! The actual hub class size lower bounds and ordered small-density margins
supply all the selection inequalities for the general-length boundary finish. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_general_selection_margins_from_sizes
    (H:V→U→Prop) (X:Finset V) (Z:Finset U) (κ ζ p ε t ν:ℝ)
    (hκ:0<κ) (hζ:0<ζ) (hp:0<p) (hp1:p≤1)
    (hu:Fintype.card U≤Fintype.card V)
    (hhub:∀j:{u:U // u∉Z},κ*Fintype.card V≤((ordinaryBoundaryHubSet H Z X j).card:ℝ))
    (hε:ε≤p^2/4) (hsmall:t+ν≤(p^2/4)*Fintype.card (V⊕U))
    (hpκ:p≤4*ζ*min (κ/2) 1)
    (hsqrt:20*Real.sqrt (2*p)≤ζ*min (κ/2) 1/2)
    (hν:ν≤ζ*min (κ/2) 1*p*Fintype.card (V⊕U)/4)
    (horder:2≤ζ*min (κ/2) 1*p*Fintype.card (V⊕U)/4):
    (p+ε)*Fintype.card (V⊕U)+(t+ν)≤(2*p)*Fintype.card (V⊕U) ∧
    (p^2+ε)*Fintype.card (V⊕U)+2*(t+ν)≤(2*p)^2*Fintype.card (V⊕U) ∧
    (∀j:{u:U // u∉Z},t+ν≤ζ*(p*(ordinaryBoundaryHubSet H Z X j).card)) ∧
    (t+ν≤ζ*(p*Fintype.card (V⊕U))) ∧
    (∀j:{u:U // u∉Z},2*((2*p)*Real.sqrt (2*p)*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*((2*p)*Real.sqrt (2*p)*Fintype.card (V⊕U))):ℝ)+ν≤ζ*(p*(ordinaryBoundaryHubSet H Z X j).card)) ∧
    (2*((2*p)*Real.sqrt (2*p)*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*((2*p)*Real.sqrt (2*p)*Fintype.card (V⊕U))):ℝ)+ν≤ζ*(p*Fintype.card (V⊕U))):=by
  let n:ℝ:=Fintype.card (V⊕U)
  let κ₀:=min (κ/2) 1
  have hκ₀:0<κ₀:=lt_min (by positivity) (by norm_num)
  have hn:0≤n:=by positivity
  have hcard:(Fintype.card (V⊕U):ℝ)≤2*Fintype.card V:=by
    simp only [Fintype.card_sum,Nat.cast_add]
    have hh:(Fintype.card U:ℝ)≤Fintype.card V:=Nat.cast_le.mpr hu
    linarith
  have hsizes (j:{u:U // u∉Z}):κ₀*n≤((ordinaryBoundaryHubSet H Z X j).card:ℝ):=by
    have ha:=mul_le_mul_of_nonneg_left hcard hκ₀.le
    have hb:=mul_le_mul_of_nonneg_right (min_le_left (κ/2) (1:ℝ)) (Nat.cast_nonneg (Fintype.card V))
    have hc:=hhub j
    dsimp only [κ₀,n] at *
    nlinarith only [ha,hb,hc]
  have hwhole:κ₀*n≤n:=by
    have hh:κ₀≤1:=min_le_right _ _
    nlinarith only [mul_le_mul_of_nonneg_right hh hn]
  have hm:=ordinary_boundary_selection_margins p ε (t+ν) ν κ₀ ζ n hp hp1 hκ₀ hζ hn hε hsmall hpκ hsqrt hν horder
  refine ⟨hm.1,hm.2.1,?_,(hm.2.2 n hwhole).1,?_,(hm.2.2 n hwhole).2⟩
  · intro j;exact (hm.2.2 _ (hsizes j)).1
  · intro j;exact (hm.2.2 _ (hsizes j)).2
end Oberwolfach
