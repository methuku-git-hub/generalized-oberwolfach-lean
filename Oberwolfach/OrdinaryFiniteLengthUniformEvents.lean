module

public import Oberwolfach.OrdinaryAssignedClassWithoutUpperMargin
public import Oberwolfach.OrdinaryFiniteLengthCommonScales

@[expose] public section
/-! One density floor, one pair of input tolerances, and one order threshold
work for every fixed short length in a bounded range. Individual host weights
and auxiliary constants remain length-specific. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryBoundedLongLengths (K:ℕ):= {m:Fin (K+1) // 3≤m.1}

theorem ordinary_uniform_events_for_bounded_lengths
    (K d:ℕ) (hK:3≤K) (hd:2≤d)
    (α ρ₀ s₀ ω ηP ηH L:ℝ) (hα:0<α) (hα1:α≤1)
    (hρ₀:0<ρ₀) (hρ₁:ρ₀≤1) (hs₀:0<s₀) (hs₁:s₀≤1/100)
    (hω:0<ω) (hηP:0<ηP) (hηH:0<ηH) (hL:0≤L)
    (θhost:OrdinaryBoundedLongLengths K→ℝ)
    (hθ:∀ m,cycleThreshold (m.1.1+1)≤θhost m):
    ∃ (β row:ℝ),0<β ∧ 0<row ∧
    β≤2*(min (α/2) (1/4))*(ρ₀*s₀/2)^4*(ρ₀*s₀/2)^4 ∧
    β≤ω*(ρ₀*s₀/2)^9/4 ∧
    ∃ (k:OrdinaryBoundedLongLengths K→ℕ)
      (βH c B:OrdinaryBoundedLongLengths K→ℝ) (N:ℕ),
    ∀ m:OrdinaryBoundedLongLengths K,
      m.1.1+3≤k m ∧ 0<βH m ∧ 0<c m ∧ 0<B m ∧
      ordinaryAssignedClassAtBound m.1.1 d K m.2 hd (θhost m) α ρ₀ s₀ ω β ηP row ηH L
        hρ₀ hs₀ (k m) (βH m) (c m) (B m) N := by
  letI : Fintype (OrdinaryBoundedLongLengths K) := by
    unfold OrdinaryBoundedLongLengths
    infer_instance
  let p:ℝ:=ρ₀*s₀/2
  have hp:0<p:=by dsimp [p];positivity
  have hp1:p≤1:=by
    have hs:s₀≤1:=by linarith
    have h:=ordinary_uniform_selected_density_floor ρ₀ s₀ hρ₀ hρ₁ hs₀ hs
    exact h.2.1
  obtain ⟨β,row,hβ,hrow,htmax,hthub,hlong⟩:=ordinary_common_scales_for_bounded_lengths K hK α p ω hα hp hp1 hω
  have hK0:0<K:=by omega
  have hdata:∀m:OrdinaryBoundedLongLengths K,∃ (k:ℕ) (βH c B:ℝ) (N:ℕ),
      m.1.1+3≤k ∧ 0<βH ∧ 0<c ∧ 0<B ∧
      ordinaryAssignedClassAtBound m.1.1 d K m.2 hd (θhost m) α ρ₀ s₀ ω β ηP row ηH L
        hρ₀ hs₀ k βH c B N := by
    intro m
    have hmK:m.1.1≤K:=by have hm:=m.1.2;omega
    have hh:=hlong m.1.1 m.2 hmK
    obtain ⟨k,βH,c,B,hk,hb,hc,hB,N,hN⟩:=ordinary_assigned_class_at_bound_without_upper_margin m.1.1 d K m.2 hd hK0
      (θhost m) α ρ₀ s₀ ω β ηP row ηH L (hθ m) hα hα1
      hρ₀ hρ₁ hs₀ hs₁ hω hβ hh.1 hh.2.1 hηP hrow hh.2.2 hηH hL
    exact ⟨k,βH,c,B,N,hk,hb,hc,hB,hN⟩
  choose k βH c B N hk hb hc hB hbound using hdata
  refine ⟨β,row,hβ,hrow,htmax,hthub,k,βH,c,B,Finset.univ.sup N,?_⟩
  intro m
  refine ⟨hk m,hb m,hc m,hB m,?_⟩
  intro n hn
  exact hbound m n ((Finset.le_sup (Finset.mem_univ m)).trans hn)
end Oberwolfach
