module

public import Oberwolfach.ExpandedBinaryColourProjection
public import Oberwolfach.GroupedProtectedPartitionTransfer

@[expose] public section
/-! Transfer the protected binary-partition event to the original expanded
sample when both colour densities have a positive lower bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance groupedExpandedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) groupedExpandedTwo : DecidableEq (Fin 2):=instDecidableEqFin 2

theorem expanded_grouped_partition_via_transfer_high_probability
    (α r ξ:ℝ) (hα:0<α) (hr:0<r) (hξ:0<ξ) (B:ℕ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U]
      (P Z:SimpleGraph (Fin n)) (D:ℕ) (m:Fin 2→ℕ)
      (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
      (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
      {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)),
      P.IsRegularOfDegree D→Even D→(1/2+α)*n≤(D:ℝ)→
      (∑a,m a)=D/2→(∀a,expandedBinaryProbability p k p₂ k₂ u a/2*D=(m a:ℝ))→
      (∀a,r≤expandedBinaryProbability p k p₂ k₂ u a)→
      (∀v,(Z.degree v:ℝ)≤α/100000*n)→
      let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
      1-1/(n:ℝ)^10≤(μ.sigma ν).probability (fun z=>
        GroupedProtectedPartitionEvent P Z m B ξ (fun e=>(expandedBinaryClass (z.1 (Sum.inl e))).1)):=by
  obtain ⟨N,hN⟩:=grouped_protected_partition_transfer α r ξ hα hr hξ B
  refine ⟨N,?_⟩
  intro n hn U Γ Color _ _ _ _ P Z D m p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS R _ ν hreg heven hmin hsize hm hrho hZ μ
  let ρ:=expandedBinaryProbability p k p₂ k₂ u
  let hρ:=expanded_binary_probability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum
  let ht:=expanded_binary_probability_sum p k p₂ k₂ u
  have hN':=hN n hn
  have hdec:instDecidableEqFin n=groupedExpandedFin n:=Subsingleton.elim _ _
  try rw [hdec] at hN'
  apply hN' P Z D m ρ hρ ht hreg heven hmin hsize hm hrho hZ (μ.sigma ν)
    (fun z e=>(expandedBinaryClass (z.1 (Sum.inl e))).1)
  intro E
  exact expanded_binary_colour_probability_after_retention p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν E
end Oberwolfach
