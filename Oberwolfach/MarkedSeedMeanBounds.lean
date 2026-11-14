module

public import Oberwolfach.MarkedParentPositionLoads
public import Oberwolfach.SuccessorSequencePositionBounds

@[expose] public section

/-! The normalized marked seed has mean between 1-τ and 1.
For spoke roots, the denominator is independent of the size of the hub domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

lemma normalized_mass_error (τ c M S : ℝ) (hc : 0≤c)
    (hlo : (1-τ)*M≤S) (hhi : S≤M) (hone : c*M=1) : |c*S-1|≤τ := by
  have h1 := mul_le_mul_of_nonneg_left hlo hc
  have h2 := mul_le_mul_of_nonneg_left hhi hc
  have hτ : 0≤τ := by nlinarith [show c*((1-τ)*M)=(1-τ)*(c*M) by ring]
  rw [abs_le]
  constructor <;> nlinarith [show c*((1-τ)*M)=(1-τ)*(c*M) by ring]

variable {V U : Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b : ℕ} {P : SimpleGraph V} {π : Equiv.Perm V} {D τ A B : ℝ}
  {weight : (Fin (m+1)→V)→ℝ}

theorem markedParent_spoke_normalized
    (hw : SuccessorSequenceWeightConditions P π b D τ A B weight)
    (hm : 0<m) (hD : 0<D) (s t : ℝ) (hs : 0<s) (ht : t=s/m)
    (j : Bool) (v : V) (u : U) :
    |(t/(D*(if j then t else s)))*
      (∑ W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π b
        (fun (_ : V) (_ : U)=>True) (fun _ _=>True),
        if Sum.inr (j,v,u)∈typedMarkedOccurrenceResources W then weight W.1.val else 0)-1|≤τ := by
  rw [markedParent_spoke_position_load m b π weight (successor_weight_zero_of_not_separated hw)]
  have hmass := successor_typed_vertex_mass hw j v
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have ht' : 0<t := by rw [ht];positivity
  apply normalized_mass_error τ _ ((if j then 1 else (m:ℝ))*D) _
  · cases j <;> positivity
  · nlinarith [hmass.1]
  · exact hmass.2
  · cases j <;> simp only [Bool.false_eq_true,ite_false,ite_true,one_mul]
    · rw [ht];field_simp
    · field_simp

theorem markedParent_marked_rim_normalized
    (hw : SuccessorSequenceWeightConditions P π b D τ A B weight)
    (hD : 0<D) (k t : ℝ) (hk : 0<k) (ht : 0≤t)
    (hbalance : (Fintype.card U:ℝ)*t=D*k)
    (x y : V) (hsep : ¬PermutationClose π b x y) (hP : P.Adj x (π y)) :
    |(t/(D*k))*
      (∑ W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π b
        (fun (_ : V) (_ : U)=>True) (fun _ _=>True),
        if Sum.inl (Sum.inr (x,y))∈typedMarkedOccurrenceResources W then weight W.1.val else 0)-1|≤τ := by
  rw [markedParent_marked_rim_position_load m b π weight (successor_weight_zero_of_not_separated hw)]
  rw [← mul_assoc]
  have hmass := successor_marked_edge_mass hw x y hsep hP
  apply normalized_mass_error τ _ 1 _ (by positivity) (by simpa using hmass.1) hmass.2
  field_simp
  nlinarith [hbalance]

theorem markedParent_ordinary_rim_normalized
    (hw : SuccessorSequenceWeightConditions P π b D τ A B weight)
    (hm : 0<m) (hD : 0<D) (p t : ℝ) (hp : 0<p) (ht : 0≤t)
    (hbalance : (Fintype.card U:ℝ)*t*m=D*p)
    (x y : V) (hsep : ¬PermutationClose π b x y) (hP : P.Adj x y) :
    |(t/(D*p))*
      (∑ W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π b
        (fun (_ : V) (_ : U)=>True) (fun _ _=>True),
        if Sum.inl (Sum.inl (x,y))∈typedMarkedOccurrenceResources W then weight W.1.val else 0)-1|≤τ := by
  rw [markedParent_ordinary_rim_position_load m b π weight (successor_weight_zero_of_not_separated hw)]
  rw [← mul_assoc]
  have hmass := successor_ordinary_edge_mass hw x y hsep hP
  apply normalized_mass_error τ _ m _ (by positivity) (by nlinarith [hmass.1]) hmass.2
  field_simp
  nlinarith [hbalance]

end Oberwolfach
