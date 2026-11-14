module

public import Oberwolfach.RawMarkedPotentialSampling
public import Oberwolfach.TypedMarkedResourceProducts

@[expose] public section

/-! The normalization factors in the marked seed expectations. The parent
weights and the denominator remain fixed when the tested root is omitted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
  {m d : ℕ} {π : Equiv.Perm V} {H₀ Hₖ : V→U→Prop}

theorem rawMarkedWheelMarginal_cycle_position
    (P : SimpleGraph V) (hm : 1≤m)
    (W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ)
    (p k : ℝ) (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color)
    (hP : ∀ i : Fin m,P.Adj (W.1.val i.castSucc) (W.1.val i.succ))
    (hK : P.Adj (W.1.val (Fin.last m)) (π (W.1.val 0)))
    (i : Fin (m+1)) :
    rawMarkedWheelMarginal P π d p k q s g j
      (Sum.inl (markedCycleTypedEdge Prod.fst Prod.snd Prod.fst Prod.snd m π (3*d) W.1 i))=
      if i=Fin.last m then k else p := by
  refine Fin.lastCases ?_ (fun i=>?_) i
  · rw [markedPairCycle_edge_marked]
    have hne : (Fin.last m : Fin (m+1))≠0 := by intro h;have hh:=congrArg Fin.val h;simp at hh;omega
    have hsep := W.1.property.1 (Fin.last m) 0 hne
    simp only [rawMarkedWheelMarginal,hsep,hK,not_false_eq_true,true_and,ite_true]
  · rw [markedPairCycle_edge_ordinary]
    have hne : i.castSucc≠i.succ := by intro h;have hh:=congrArg Fin.val h;simp at hh
    have hsep := W.1.property.1 i.castSucc i.succ hne
    simp only [rawMarkedWheelMarginal,hsep,hP,not_false_eq_true,true_and,ite_true,Fin.castSucc_ne_last,ite_false]

theorem rawMarkedWheelMarginal_spoke_position
    (P : SimpleGraph V)
    (W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ)
    (p k s₀ t₀ : ℝ) (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color)
    (hq : ∀ u,q u g=t₀) (hs : ∀ u,s u j=s₀) (i : Fin (m+1)) :
    rawMarkedWheelMarginal P π d p k q s g j (Sum.inr (decide (i=0),W.1.val i,W.2.val))=
      if i=0 then t₀ else s₀ := by
  simp [rawMarkedWheelMarginal,hq,hs]

theorem rawMarkedSeed_candidate_mean
    (P : SimpleGraph V) (hm : 1≤m)
    (W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ)
    (p k s₀ t₀ D w₀ : ℝ) (hp : p≠0) (hk : k≠0) (hs₀ : s₀≠0) (hD : D≠0)
    (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color)
    (hq : ∀ u,q u g=t₀) (hs : ∀ u,s u j=s₀)
    (hP : ∀ i : Fin m,P.Adj (W.1.val i.castSucc) (W.1.val i.succ))
    (hK : P.Adj (W.1.val (Fin.last m)) (π (W.1.val 0)))
    (root : ((V×V)⊕(V×V))⊕(Bool×V×U)) (hroot : root∈typedMarkedOccurrenceResources W)
    (hφ : rawMarkedWheelMarginal P π d p k q s g j root≠0) :
    (w₀/(D*p^m*k*s₀^m)) *
      (∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p k q s g j a)=
      w₀*t₀/(D*rawMarkedWheelMarginal P π d p k q s g j root) := by
  have hh := typedMarkedResource_product_omitted W (rawMarkedWheelMarginal P π d p k q s g j)
    p k s₀ t₀ (rawMarkedWheelMarginal_cycle_position P hm W p k q s g j hP hK)
    (rawMarkedWheelMarginal_spoke_position P W p k s₀ t₀ q s g j hq hs) root hroot hφ
  have hh' : (∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p k q s g j a)=
      (p^m*k)*(t₀*s₀^m)/rawMarkedWheelMarginal P π d p k q s g j root := by
    convert hh using 1
    apply Finset.prod_congr (by ext a;simp)
    intro a _
    rfl
  rw [hh']
  field_simp

end Oberwolfach
