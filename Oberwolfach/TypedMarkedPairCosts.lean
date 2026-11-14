module

public import Oberwolfach.TypedMarkedPotentialResources

@[expose] public section

/-! Bounds on pairs of typed potential resources, preserving the two spoke
labels and allowing collisions between physical images of different candidates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
  {H₀ Hₖ : V → U → Prop}
  (hm : 3≤m) (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
  (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
  (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
include hm hn hB hw

include hu in
theorem typedMarkedPair_rim_rim (e f : E⊕K) :
    resourceOmittedPairWeight typedMarkedOccurrenceResources w (Sum.inl e) (Sum.inl f)≤
      if Sum.elim tail ktail f∈({Sum.elim tail ktail e,Sum.elim head khead e}:Finset V) ∨
        Sum.elim head khead f∈({Sum.elim tail ktail e,Sum.elim head khead e}:Finset V)
      then ((m:ℝ)+1)^4*B/Fintype.card V else ((m:ℝ)+1)^4*B/(Fintype.card V:ℝ)^2 := by
  have hh := typedMarkedOmittedPair_le w (fun W=>(hw W).1) (Sum.inl e) (Sum.inl f)
  simp only [forgetMarkedSpokeType,Sum.map_inl,id_eq,canonicalMarkedOmittedPair_rims] at hh
  exact hh.trans (canonical_marked_rim_rim_pair_cost hm hn hu w B hB (fun W=>(hw W).2) e f)

theorem typedMarkedPair_rim_spoke (e : E⊕K) (j : Bool) (v : V) (u : U) :
    resourceOmittedPairWeight typedMarkedOccurrenceResources w (Sum.inl e) (Sum.inr (j,v,u))≤
      if v∈({Sum.elim tail ktail e,Sum.elim head khead e}:Finset V)
      then ((m:ℝ)+1)^4*B/Fintype.card V else ((m:ℝ)+1)^4*B/(Fintype.card V:ℝ)^2 := by
  have hh := typedMarkedOmittedPair_le w (fun W=>(hw W).1) (Sum.inl e) (Sum.inr (j,v,u))
  simp only [forgetMarkedSpokeType,Sum.map_inl,Sum.map_inr,id_eq,canonicalMarkedOmittedPair_rim_spoke] at hh
  exact hh.trans (canonical_marked_rim_spoke_pair_cost hm hn w B hB (fun W=>(hw W).2) e v u)

theorem typedMarkedPair_spoke_rim (e : E⊕K) (j : Bool) (v : V) (u : U) :
    resourceOmittedPairWeight typedMarkedOccurrenceResources w (Sum.inr (j,v,u)) (Sum.inl e)≤
      if Sum.elim tail ktail e=v ∨ Sum.elim head khead e=v
      then ((m:ℝ)+1)^4*B/Fintype.card V else ((m:ℝ)+1)^4*B/(Fintype.card V:ℝ)^2 := by
  have hh := typedMarkedOmittedPair_le w (fun W=>(hw W).1) (Sum.inr (j,v,u)) (Sum.inl e)
  simp only [forgetMarkedSpokeType,Sum.map_inl,Sum.map_inr,id_eq,canonicalMarkedOmittedPair_spoke_rim] at hh
  exact hh.trans (canonical_marked_spoke_rim_pair_cost hm hn w B hB (fun W=>(hw W).2) e v u)

theorem typedMarkedPair_spoke_spoke (j k : Bool) (v x : V) (u t : U) :
    resourceOmittedPairWeight typedMarkedOccurrenceResources w (Sum.inr (j,v,u)) (Sum.inr (k,x,t))≤
      if t=u then ((m:ℝ)+1)^4*B/Fintype.card V else 0 := by
  have hh := typedMarkedOmittedPair_le w (fun W=>(hw W).1) (Sum.inr (j,v,u)) (Sum.inr (k,x,t))
  simp only [forgetMarkedSpokeType,Sum.map_inr,canonicalMarkedOmittedPair_spokes] at hh
  exact hh.trans (marked_spoke_spoke_pair_cost hm hn w B hB (fun W=>(hw W).2) v x u t)

end Oberwolfach
