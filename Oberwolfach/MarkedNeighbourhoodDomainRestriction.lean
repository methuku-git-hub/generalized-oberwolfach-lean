module

public import Oberwolfach.FiniteCenteredDomainRestriction
public import Oberwolfach.MarkedNeighbourhoodSpokeChanges

@[expose] public section

/-! Removing vertices from a summation domain changes the absolute error by
at most the number removed. All original requests and density values remain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem markedRowsWithSpokes_domain_restriction
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (A A₀:Finset V) (hA:A⊆A₀)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (err:ℝ)
    (hp:0≤p∧p≤1) (hk:0≤k∧k≤1) (hq:∀ u,0≤q u g∧q u g≤1) (hs:∀ u,0≤s u j∧s u j≤1)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h A₀ p k q s g j err σ H):
    MarkedRowsWithSpokes P π d h A p k q s g j (err+(A₀\A).card) σ H:=by
  intro S T J hS hT hJ hinj
  let eligible:=fun z=>(∀ a∈S,markedRowEligible P π (3*d) a z)∧
    Set.InjOn (fun a=>markedPairPhysical π (markedRowRim a z)) S∧
    (∀ a∈T,Sum.elim (fun xy=>P.Adj xy.1 xy.2) (fun xy=>P.Adj xy.1 (π xy.2)) (markedRowRim a z))
  let present:=fun z=>(∀ a∈S,rawMarkedPairRims P π d σ (markedRowRim a z))∧(∀ a∈J,H a.1 z a.2)
  let target:ℝ:=(∏ a∈S,if a.1 then k else p)*(∏ a∈J,if a.1 then q a.2 g else s a.2 j)
  have hR (a:Bool×Bool×V):0≤(if a.1 then k else p)∧(if a.1 then k else p)≤1:=by
    split_ifs <;> assumption
  have hSp (a:Bool×U):0≤(if a.1 then q a.2 g else s a.2 j)∧(if a.1 then q a.2 g else s a.2 j)≤1:=by
    split_ifs <;> first | exact hq a.2 | exact hs a.2
  have ht:0≤target∧target≤1:=by
    have hR0:=Finset.prod_nonneg (fun a (_:a∈S)=>(hR a).1)
    have hR1:=Finset.prod_le_one₀ (fun a (_:a∈S)=>(hR a).1) (fun a (_:a∈S)=>(hR a).2)
    have hS0:=Finset.prod_nonneg (fun a (_:a∈J)=>(hSp a).1)
    have hS1:=Finset.prod_le_one₀ (fun a (_:a∈J)=>(hSp a).1) (fun a (_:a∈J)=>(hSp a).2)
    exact ⟨mul_nonneg hR0 hS0,(mul_le_mul hR1 hS1 hS0 (by norm_num)).trans_eq (one_mul 1)⟩
  have hh:=finite_centered_count_restriction A A₀ hA eligible present (fun _=>target)
    (fun _ _=>ht) err (by
      simpa only [eligible,present,target,markedRowCountWithSpokes,markedRowDomain,
        Finset.sum_const,nsmul_eq_mul,mul_comm] using hr S T J hS hT hJ hinj)
  simpa only [eligible,present,target,markedRowCountWithSpokes,markedRowDomain,
    Finset.sum_const,nsmul_eq_mul,mul_comm] using hh

theorem markedIndicesWithSpokes_domain_restriction
    (π:Equiv.Perm V) (d h:ℕ) (B B₀:Finset U) (hB:B⊆B₀)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (err:ℝ)
    (hq:∀ u,0≤q u g∧q u g≤1) (hs:∀ u,0≤s u j∧s u j≤1)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hi:MarkedIndicesWithSpokes π d h B₀ q s g j err σ H):
    MarkedIndicesWithSpokes π d h B q s g j (err+(B₀\B).card) σ H:=by
  intro J hJ hsep
  let target:=fun u=>∏ a∈J,if a.1 then q u g else s u j
  have ht (u:U):0≤target u∧target u≤1:=by
    have hp (a:Bool×V):0≤(if a.1 then q u g else s u j)∧(if a.1 then q u g else s u j)≤1:=by
      split_ifs <;> first | exact hq u | exact hs u
    exact ⟨Finset.prod_nonneg (fun a _=>(hp a).1),
      Finset.prod_le_one₀ (fun a _=>(hp a).1) (fun a _=>(hp a).2)⟩
  have hh:=finite_centered_count_restriction B B₀ hB (fun _=>True) (fun u=>∀ a∈J,H a.1 a.2 u)
    target (fun u _=>ht u) err (by simpa only [Finset.filter_true,target,markedIndexCountWithSpokes] using hi J hJ hsep)
  simpa only [Finset.filter_true,target,markedIndexCountWithSpokes] using hh

end Oberwolfach
