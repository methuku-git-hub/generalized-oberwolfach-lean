module

public import Oberwolfach.GroupedRegularClassTransfer
public import Oberwolfach.JointEventPolynomialMargins

@[expose] public section
/-! The protected regular class has any prescribed positive failure budget
for sufficiently large hosts, uniformly over later bounded protected edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem grouped_regular_class_arbitrary_failure
    (α r ξ η:ℝ) (hα:0<α) (hr:0<r) (hξ:0<ξ) (hη:0<η) (B:ℕ):
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
      1-η≤μ.probability (fun z=>∀A:SimpleGraph (Fin n),(∀v,A.degree v≤B)→
        ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*m 0) ∧
          (∀x y,(Z⊔A).Adj x y→(S.Adj x y↔(longPhysicalStateGraph P (σ z) {0,1,2,3,4}).Adj x y)) ∧
          (∀v,((changed ((longPhysicalStateGraph P (σ z) {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)):= by
  obtain ⟨Npart,hPart⟩:=grouped_regular_class_transfer α r ξ hα hr hξ B
  obtain ⟨Nsmall,_,hSmall⟩:=joint_event_polynomial_margin (1-η) 1 0 10 1 (by linarith) (by norm_num) (by norm_num)
  refine ⟨max Npart Nsmall,?_⟩
  intro n hn U Γ Color _ _ _ _ P Z D m ρ hρ ht hreg heven hmin hsum hm hrho hZ Ω _ μ σ hproj
  have hGroup:=hPart n (by omega) U Γ Color P Z D m ρ hρ ht hreg heven hmin hsum hm hrho hZ μ σ hproj
  have hsmall:=hSmall n (by omega)
  have hpow:(n:ℝ)^(-(10:ℝ))=1/(n:ℝ)^10:=by rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]; congr 1 <;> norm_num
  rw [hpow] at hsmall
  simp only [one_mul,zero_mul,add_zero] at hsmall
  have hcompare:1-η≤1-1/(n:ℝ)^10:=by linarith only [hsmall]
  exact hcompare.trans hGroup
end Oberwolfach
