module

public import Oberwolfach.FirstVortexIndicesNonempty
public import Oberwolfach.ExpandedBoundaryHubsLocalSmallFailure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_first_vortex_boundary_all_roots_high_probability
    (d:ℕ) (hd:2≤d) (ε ρ₀ failure:ℝ) (hε:0<ε) (hρ₀:0<ρ₀) (hfailure:0<failure):
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U Color:Type) [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Color],
    ∀(G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D → 0<Fintype.card V → (Fintype.card V:ℝ)/2≤D → 0<D →
    ρ₀ ≤ initialIndexDensity U D → initialIndexDensity U D≤1 →
    0≤β → β≤1/4 → 0<m → m₀≤Fintype.card V →
    ∀(π:Equiv.Perm V) (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Bool Color→Type) [∀a,Fintype (F a)] (ν:∀a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-failure≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀v,
      ((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) (Q.extendedIndices 1) v).card:ℝ)≤
      4*((Q.extendedIndices 1).card:ℝ)/d+4*(Fintype.card V:ℝ)^(3/4:ℝ)) :=by
  obtain ⟨m₀,hm₀,hBound⟩:=raw_expanded_boundary_hubs_local_small_failure d hd failure hfailure
  refine ⟨m₀,hm₀,?_⟩
  intro V U Color _ _ _ _ _ G D m β Q hreg hn hD hDpos hρ hρhi hβ hβ1 hm hsize π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F _ ν μ f
  have hJ:(Q.extendedIndices 1).Nonempty:=Q.first_inner_indices_nonempty hreg hn hD hρ₀ hρ hβ hβ1 hε hm
  have hJA:(Q.extendedIndices 1).card≤(Q.extendedVertices 1).card:=by
    have hh:=Q.extended_index_size_upper hreg hn hDpos hε.le hρhi 1
    omega
  let A:Unit→Finset V:=fun _=>Finset.univ
  let J:Unit→Finset U:=fun _=>Q.extendedIndices 1
  have hmin:∀i∈(Finset.univ:Finset Unit),m₀≤(A i).card:=by intro i hi;simpa [A] using hsize
  have hinj:Set.InjOn (fun i=>(A i).card) (Finset.univ:Finset Unit):=by intro i hi j hj hij; exact Subsingleton.elim i j
  have hpos:∀i∈(Finset.univ:Finset Unit),0<(J i).card:=by intro i hi;exact hJ.card_pos
  have hle:∀i∈(Finset.univ:Finset Unit),(J i).card≤(A i).card:=by intro i hi;simpa [A,J] using (hJA.trans (Finset.card_le_univ (Q.extendedVertices 1)))
  have hh:=hBound V U Color Unit Finset.univ A J hmin hinj hpos hle π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F ν
  simpa only [A,J,Finset.mem_univ,forall_const,Finset.card_univ] using hh
end Oberwolfach
