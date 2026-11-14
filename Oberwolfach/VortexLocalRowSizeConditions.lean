module

public import Oberwolfach.VortexProtectedGeometry

@[expose] public section
/-! Distinct, comparable vortex sizes for local row concentration. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem Vortex.extended_previous_card_le
    {V U:Type} [Fintype V] [Fintype U] {G:SimpleGraph V}
    {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m) (he:0<ε)
    {i:ℕ} (hi:1 ≤ i) (hL:i≤Q.length) (hpos:1≤(Q.extendedVertices i).card) :
    ((Q.extendedVertices (i-1)).card:ℝ)≤(2/ε)*(Q.extendedVertices i).card := by
  have hprev:i-1≤Q.length:=by omega
  have hsuc:i-1+1=i:=by omega
  have hf:=Nat.lt_floor_add_one (ε * (floorOrbit ε (Fintype.card V) (i-1):ℝ))
  rw [← floorOrbit_succ, hsuc, ← Q.sizes (i-1) hprev, ← Q.sizes i hL] at hf
  rw [Q.extendedVertices_eq hprev, Q.extendedVertices_eq hL] at *
  have hp:(1:ℝ)≤(Q.vertices i).card:=by exact_mod_cast hpos
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ he).2
  nlinarith

theorem Vortex.extended_card_injOn_positive
    {V U:Type} [Fintype V] [Fintype U] {G:SimpleGraph V}
    {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m) (he:0≤ε) (heq:ε≤1/4)
    (T:Finset ℕ) (hpos:∀i∈T,1≤(Q.extendedVertices i).card) :
    Set.InjOn (fun i=>(Q.extendedVertices i).card) T := by
  intro i hi j hj hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · have hh:=Q.extended_later_size_le_quarter he heq hijlt
    have hp:(1:ℝ)≤(Q.extendedVertices i).card:=by exact_mod_cast hpos i hi
    have heq' : ((Q.extendedVertices i).card:ℝ)=((Q.extendedVertices j).card:ℝ):=by exact_mod_cast hij
    linarith
  · have hh:=Q.extended_later_size_le_quarter he heq hjilt
    have hp:(1:ℝ)≤(Q.extendedVertices j).card:=by exact_mod_cast hpos j hj
    have heq' : ((Q.extendedVertices i).card:ℝ)=((Q.extendedVertices j).card:ℝ):=by exact_mod_cast hij
    linarith

theorem Vortex.extended_card_at_least_threshold
    {V U:Type} [Fintype V] [Fintype U] {G:SimpleGraph V}
    {D mv m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε mv)
    (hm:(m:ℝ)≤ε*mv/2) {i:ℕ} (hi:i≤Q.length) :
    m≤(Q.extendedVertices i).card := by
  have ht:(m:ℝ)≤(Q.vertices Q.length).card:=le_trans hm Q.terminal_lower
  have htN:m≤(Q.vertices Q.length).card:=by exact_mod_cast ht
  have hsub:=Q.extendedVertices_subset hi
  rw [Q.extendedVertices_eq (le_refl Q.length)] at hsub
  exact htN.trans (Finset.card_le_card hsub)
end Oberwolfach
