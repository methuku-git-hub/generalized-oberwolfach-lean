module

public import Oberwolfach.LongReservedContinuationSeparatedScales
public import Oberwolfach.PartitionMargins

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_reserved_continuation_all_margins
    (γ pstar:ℝ) (hγ:0<γ) (hp:0<pstar):
    ∃β lamList ζList βfinal δ:ℝ,
      0<β ∧ β≤1 ∧ 0<lamList ∧ lamList≤1/100 ∧ 0<ζList ∧
      0<βfinal ∧ βfinal≤1 ∧ 0<δ ∧ δ≤(βfinal/100)^2 ∧ δ≤1/100 ∧
    ∃dMin L₀:ℕ,
      (∀m:ℕ,L₀≤m→4/(m:ℝ)≤δ/4 ∧ 1/(100*(m:ℝ))≤lamList/8) ∧
      (∀m:ℕ,L₀≤m→∀ε:ℝ,ε≤lamList/8→
        βfinal+ε+1/(100*(m:ℝ))+lamList/8≤lamList) ∧
      ∀d:ℕ,dMin≤d→2≤d→∃N:ℕ,∀n:ℕ,N≤n→
        2≤n ∧ 100/βfinal≤(n:ℝ) ∧ 2/Real.sqrt δ≤(n:ℝ) ∧
        (n:ℝ)^(3/4:ℝ)≤(lamList/8)*n ∧
        (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n ∧
        β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*(1/100:ℝ) ∧
        (lamList+2*ζList)*n≤β*n :=by
  obtain ⟨β,lamList,ζList,βfinal,δ,hβ,hβ1,hlam,hlam1,hζ,hβfinal,hβquarter,hδ,hδbound,hδ1,dMin,L₀,hM,htrim,hList⟩:=
    long_reserved_continuation_separated_scales γ pstar hγ hp
  have hβfinal1:βfinal≤1:=by linarith
  obtain ⟨Npower,hPower⟩:=eventually_sublinear_le_linear (p:=(3/4:ℝ)) (ε:=lamList/8) (by norm_num) (by positivity)
  obtain ⟨Nβ,hNβ⟩:=exists_nat_gt (100/βfinal)
  obtain ⟨Nδ,hNδ⟩:=exists_nat_gt (2/Real.sqrt δ)
  refine ⟨β,lamList,ζList,βfinal,δ,hβ,hβ1,hlam,hlam1,hζ,hβfinal,hβfinal1,hδ,hδbound,hδ1,dMin,L₀,hM,?_,?_⟩
  · intro m hm ε hε
    exact htrim m hm ε (lamList/8) hε (le_refl _)
  · intro d hdmin hd
    obtain ⟨Nlist,hListN⟩:=hList d hdmin hd
    refine ⟨max (max (max (max Nlist Npower) Nβ) Nδ) 2,?_⟩
    intro n hn
    have hnl:Nlist≤n:=by omega
    have hnp:Npower≤n:=by omega
    have hnb:Nβ≤n:=by omega
    have hnd:Nδ≤n:=by omega
    have hnbR:(Nβ:ℝ)≤n:=by exact_mod_cast hnb
    have hndR:(Nδ:ℝ)≤n:=by exact_mod_cast hnd
    have hlist:=hListN n hnl
    have hnonneg:(0:ℝ)≤(n:ℝ)/(8*(d:ℝ))+2*(n:ℝ)^(3/4:ℝ)/d:=by positivity
    exact ⟨by omega,le_trans hNβ.le hnbR,le_trans hNδ.le hndR,hPower n hnp,hlist.1,hlist.2.1,by linarith [hlist.2.2]⟩
end Oberwolfach
