module

public import Oberwolfach.GroupedProtectedPartitionEvent

@[expose] public section
/-! A protected binary partition transfers along any exact colour-law
projection, including a dependent retained experiment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem grouped_protected_partition_transfer
    (α r ξ:ℝ) (hα:0<α) (hr:0<r) (hξ:0<ξ) (B:ℕ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(P Z:SimpleGraph (Fin n)) (D:ℕ) (m:Fin 2→ℕ)
      (ρ:Fin 2→ℝ) (hρ:∀a,0≤ρ a) (ht:∑a,ρ a=1),
      P.IsRegularOfDegree D→Even D→(1/2+α)*n≤(D:ℝ)→
      (∑a,m a)=D/2→(∀a,ρ a/2*D=(m a:ℝ))→(∀a,r≤ρ a)→
      (∀v,(Z.degree v:ℝ)≤α/100000*n)→
      ∀{Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω) (col:Ω→Sym2 (Fin n)→Fin 2),
      (∀E:(Sym2 (Fin n)→Fin 2)→Prop,μ.probability (fun z=>E (col z))=
        (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.categorical ρ hρ ht)).probability E)→
      1-1/(n:ℝ)^10≤μ.probability (fun z=>GroupedProtectedPartitionEvent P Z m B ξ (col z)):=by
  obtain ⟨N,hN⟩:=protectedRegularPartition_highProbability 2 hα hr hξ B
  refine ⟨N,?_⟩
  intro n hn P Z D m ρ hρ ht hreg heven hmin hsum hm hrho hZ Ω _ μ col hproj
  rw [hproj]
  exact hN n hn P Z D m ρ hρ ht hreg heven hmin hsum hm hrho hZ
end Oberwolfach
