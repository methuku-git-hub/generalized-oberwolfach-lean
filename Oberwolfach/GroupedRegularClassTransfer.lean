module

public import Oberwolfach.GroupedProtectedPartitionTransfer
public import Oberwolfach.GroupedRegularClassExtraction

@[expose] public section
/-! An exact grouped-colour law gives the protected regular sampled-class
witness when both grouped densities meet the partition lower bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem grouped_regular_class_transfer
    (α r ξ:ℝ) (hα:0<α) (hr:0<r) (hξ:0<ξ) (B:ℕ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U Γ Color:Type) [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
      (P Z:SimpleGraph (Fin n)) (D:ℕ) (m:Fin 2→ℕ)
      (ρ:Fin 2→ℝ) (hρ:∀a,0≤ρ a) (ht:∑a,ρ a=1),
      P.IsRegularOfDegree D→Even D→(1/2+α)*n≤(D:ℝ)→
      (∑a,m a)=D/2→(∀a,ρ a/2*D=(m a:ℝ))→(∀a,r≤ρ a)→
      (∀v,(Z.degree v:ℝ)≤α/100000*n)→
      ∀{Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω)
        (σ:Ω→∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e),
      (∀E:(Sym2 (Fin n)→Fin 2)→Prop,
        μ.probability (fun z=>E (fun e=>(expandedBinaryClass (σ z (Sum.inl e))).1))=
        (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.categorical ρ hρ ht)).probability E)→
      1-1/(n:ℝ)^10≤μ.probability (fun z=>∀A:SimpleGraph (Fin n),(∀v,A.degree v≤B)→
        ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*m 0) ∧
          (∀x y,(Z⊔A).Adj x y→(S.Adj x y↔(longPhysicalStateGraph P (σ z) {0,1,2,3,4}).Adj x y)) ∧
          (∀v,((changed ((longPhysicalStateGraph P (σ z) {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)):=by
  obtain ⟨N,hN⟩:=grouped_protected_partition_transfer α r ξ hα hr hξ B
  refine ⟨N,?_⟩
  intro n hn U Γ Color _ _ _ _ P Z D m ρ hρ ht hreg heven hmin hsum hm hrho hZ Ω _ μ σ hproj
  have hh:=hN n hn P Z D m ρ hρ ht hreg heven hmin hsum hm hrho hZ μ
    (fun z e=>(expandedBinaryClass (σ z (Sum.inl e))).1) hproj
  apply hh.trans
  apply finiteLaw_probability_mono
  intro z hz A hA
  obtain ⟨H,hpart,hregular,hprotect,hedit⟩:=hz A hA
  exact grouped_regular_class_extraction P Z A (σ z) m H ξ hpart hregular hprotect hedit
end Oberwolfach
