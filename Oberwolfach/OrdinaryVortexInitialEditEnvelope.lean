module

public import Oberwolfach.OrdinaryFixedVortexCleanupDomainGeometry

@[expose] public section
/-! The initial correction's fixed conflict term and two-sided edit cap fit
an earlier inner-scale envelope once the terminal size is large enough. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_initial_edit_envelope
    (ε ρ₀ cap:ℝ) (d:ℕ) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hcap:0<cap):
    ∀β:ℝ,0 ≤ β  →  β ≤ 1/4  →  ∃m₀:ℕ,1 ≤ m₀ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D  →  0<Fintype.card V  → 
      (Fintype.card V:ℝ)/2 ≤ D  →  ρ₀ ≤ initialIndexDensity U D  →  initialIndexDensity U D ≤ 1  →  m₀ ≤ m  → 
    ∀(Q:Vortex U P D β ε m) (i:ℕ),i<Q.length  →  ∀δcap:ℝ,0 ≤ δcap  →  δcap ≤ cap/2  → 
    let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    let L:=2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card;
    0 ≤ L ∧ L ≤ cap*I.card :=by
  intro β hβ hβ1
  obtain ⟨N,hN⟩:=exists_nat_ge (4*((3*d:ℕ):ℝ)/cap)
  obtain ⟨m₀,hm₀,hsize⟩:=ordinary_fixed_vortex_cleanup_domain_geometry β ε ρ₀ hβ hβ1 hε hε1 hρ₀ N
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ P D m hreg hn hD hρlo hρhi hm Q i hi δcap hδ hδcap I B L
  have hs:=hsize V U P D m hreg hn hD hρlo hρhi hm Q i hi
  have hI:(N:ℝ) ≤ I.card:=by exact_mod_cast hs.2.2.1
  have hfixed:2*((3*d:ℕ):ℝ) ≤ (cap/2)*I.card:=by
    have hh:4*((3*d:ℕ):ℝ) ≤ cap*(N:ℝ):=by simpa [mul_comm] using (div_le_iff₀ hcap).mp hN
    have ht:=mul_le_mul_of_nonneg_left hI hcap.le
    nlinarith only [hh,ht]
  have hmin0:0 ≤ min (I.card:ℝ) B.card:=by positivity
  have hmin:min (I.card:ℝ) B.card ≤ I.card:=min_le_left _ _
  have hδI:δcap*min (I.card:ℝ) B.card ≤ (cap/2)*I.card:=by
    have hh:=mul_le_mul_of_nonneg_left hmin hδ
    have ht:=mul_le_mul_of_nonneg_right hδcap (show (0:ℝ) ≤ I.card by positivity)
    exact hh.trans ht
  constructor
  · dsimp [L];positivity
  · dsimp [L];nlinarith only [hfixed,hδI]
end Oberwolfach
