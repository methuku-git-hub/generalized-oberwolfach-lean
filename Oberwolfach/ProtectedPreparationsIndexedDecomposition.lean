module

public import Oberwolfach.ProtectedFactorPreparation

@[expose] public section
/-! Conditional final assembly: high-probability robust class events and the
protected partition are realized on one colouring, then reassembled into the
original prescribed factor family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem protected_factor_preparations_imply_indexed_decomposition (K:ℕ) {α r ξ:ℝ}
    (hα:0<α) (hr:0<r) (hξ:0<ξ) (B:ℕ):
    ∃N₀:ℕ,∀k:ℕ,0<k→k≤K+1→∀n≥N₀,
    ∀(G:SimpleGraph (Fin n)) (D q:ℕ) (colour:Fin q→Fin k) (F:Fin q→SimpleGraph (Fin n)),
    let m:Fin k→ℕ:=fun a=>Fintype.card {i:Fin q // colour i=a}
    let Fc:∀a,Fin (m a)→SimpleGraph (Fin n):=fun a j=>F ((Fintype.equivFin {i:Fin q // colour i=a}).symm j).val;
    ∀(ρ:Fin k→ℝ) (hρ:∀a,0≤ρ a) (htotal:∑a,ρ a=1),
      G.IsRegularOfDegree D→Even D→(1/2+α)*n≤(D:ℝ)→
      (∑a,m a=D/2)→(∀a,ρ a/2*D=(m a:ℝ))→(∀a,r≤ρ a)→
    ∀I:Fin k→Finset (Fin n),((∑a,(I a).card:ℕ):ℝ)≤α/100000*n→
    ∀(Ba:Fin k→ℕ) (err:Fin k→ℝ), (∑a,Ba a≤B)→
      (∀a,1-err a≤
        (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (ρ a) (hρ a)
          (by have h:=Finset.single_le_sum (fun b _=>hρ b) (Finset.mem_univ a);linarith))).probability
            (fun σ=>ProtectedFactorPreparation G (retainedGraph G σ) (I a) ξ (Ba a) (Fc a)))→
      1/(n:ℝ)^10+(∑a,err a)<1→
    ∃c:Sym2 (Fin n)→Fin k,
      (∀a,ProtectedFactorPreparation G (edgeColourGraph G c a) (I a) ξ (Ba a) (Fc a)) ∧
      HasFactorDecomposition G F :=by
  obtain ⟨N₀,hN₀⟩:=protected_partition_indexed_family_same_colour K hα hr hξ B
  refine ⟨N₀,?_⟩
  intro k hk hkK n hn G D q colour F m Fc ρ hρ htotal hG hEven hdegree hsum hρm hρlo I hI Ba err hB hClass hbudget
  apply hN₀ k hk hkK n hn G D q colour F ρ hρ htotal hG hEven hdegree hsum hρm hρlo I hI
    (fun a S=>ProtectedFactorPreparation G S (I a) ξ (Ba a) (Fc a)) err hClass hbudget Ba hB
  intro a S hReady
  exact hReady
end Oberwolfach
