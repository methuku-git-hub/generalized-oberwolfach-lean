module

public import Oberwolfach.SequentialRowCover
public import Oberwolfach.OrdinaryRowRootAfterDeletion
public import Oberwolfach.RowComparisonCover

@[expose] public section

/-! Successive ordinary row-root covers from fixed degree, cut and
common-neighbour bounds. Every one-root choice is supplied by the proved
Hall and capped-path constructions. Comparison edges at previous roots
are excluded by the proved support statement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_row_covers_from_fixed_counts (lam:ℝ) (hlam:0<lam) :
    ∀ d:ℕ,∃ N:ℕ,∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      ∀ (Q F:SimpleGraph V) (H:V→U→Prop) (r K n:ℕ),4≤r → 0<K →
      ∀ (x:Fin n→V) (A:Finset V),Function.Injective x → (∀ i,x i∉A) →
      (∀ i,Q.neighborFinset (x i)⊆A) →
      ∀ b:ℝ,
      let T:=fun i=>Finset.univ.filter (H (x i))
      let L:ℝ:=n*max (2*(K+1)) r
      (∀ i,N≤(T i).card) → (∀ i,Q.degree (x i)=2*(T i).card) →
      (∀ a,F.degree a≤d) → (∀ i a,Q.Adj (x i) a → ¬F.Adj (x i) a) →
      (∀ i a,Q.Adj (x i) a → 2*lam*(T i).card≤(((T i).filter (H a)).card:ℝ)) →
      (∀ i u,u∈T i → 4*lam*(T i).card≤(((Q.neighborFinset (x i)).filter (fun a=>H a u)).card:ℝ)) →
      (∀ i,∀ S⊆Q.neighborFinset (x i),∀ J⊆T i,
        lam/16*(T i).card≤(S.card:ℝ) → lam/16*(T i).card≤(J.card:ℝ) →
        2*lam*S.card*J.card≤(bipartiteMatrixCut (fun a u=>if H a u then 1 else 0) S J:ℝ)) →
      (∀ i u,u∈T i → ∀ a,a≠x i → ∀ c,c≠x i →
        b≤(((A.filter (fun z=>H z u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)) →
      (∀ i,L≤lam*(T i).card) → (∀ i,L≤lam^2*(T i).card/16) →
      (∀ i,((T i).card*r:ℕ)/(K:ℝ)+((r:ℝ)+3)*(d+1)+4*(K+1)+3*L<b) →
      ∃ C:Fin n→Finset (OrdinaryWheel Q F H r),
        (∀ i,OrdinaryRowCover (C i) (x i) A K) ∧
        (∀ i j,i≠j → Disjoint ((C i).biUnion ordinaryWheelResources) ((C j).biUnion ordinaryWheelResources)) := by
  intro d
  obtain ⟨N,hN⟩:=ordinary_row_root_after_deletion lam hlam d
  refine ⟨N,?_⟩
  intro V U _ _ _ _ Q F H r K n hr hK x A hx hxA hSA b T L hn hbal hF hFx hrow hcol hcut hcount hLrow hLcut hbudget
  have hL:0≤L:=by dsimp [L];positivity
  have hLr:(n*(2*(K+1)):ℕ)≤L:=by
    dsimp [L]
    exact_mod_cast Nat.mul_le_mul_left n (le_max_left (2*(K+1)) r)
  have hLs:(n*(K+1):ℕ)≤L:=by
    have hh:n*(K+1)≤n*(2*(K+1)):=Nat.mul_le_mul_left n (by omega)
    exact (Nat.cast_le.mpr hh).trans hLr
  have hLc:(n*r:ℕ)≤L:=by
    dsimp [L]
    exact_mod_cast Nat.mul_le_mul_left n (le_max_right (2*(K+1)) r)
  apply sequential_ordinary_row_covers x hx A hxA
  intro i M havoid hMr hMs hMc
  let D:=spanningRestriction (ordinaryWheelRimGraph M) A
  let E:V→U→Prop:=fun a u=>a∈A∧ordinaryPackingSpokes M a u
  have hD (a:V):(D.degree a:ℝ)≤L:=spanningRestriction_degree_bound _ A L hL
    (fun a ha=>(Nat.cast_le.mpr (hMr a ha)).trans hLr) a
  have hEr (a:V):((Finset.univ.filter (E a)).card:ℝ)≤L:=restricted_spoke_row_bound _ A L hL
    (fun a ha=>(Nat.cast_le.mpr (hMs a ha)).trans hLs) a
  have hEc (u:U):((Finset.univ.filter (fun a=>E a u)).card:ℝ)≤L:=restricted_spoke_column_bound _ A L
    (fun u=>(Nat.cast_le.mpr (hMc u)).trans hLc) u
  have hxD (a:V):¬D.Adj (x i) a:=by
    intro ha;exact hxA i ((spanningRestriction_adj _ A (x i) a).mp ha).2.1
  have hxE (u:U):¬E (x i) u:=fun hu=>hxA i hu.1
  obtain ⟨C,hCs,hCh,hdis,hCr,hCt,hCg,hCout,hCin⟩:=hN V U Q F H r K hr hK (x i) A (hxA i) (hSA i)
    b L (hn i) (hbal i) hF (hFx i) (hrow i) (hcol i) (hcut i) (hcount i) hL (hLrow i) (hLcut i) (hbudget i)
    D E (by convert hD using 1 <;> congr!) (by convert hEr using 1 <;> congr!) (by convert hEc using 1 <;> congr!) hxD hxE
  exact row_comparison_cover_image M A (x i) K havoid C hCs hdis hCr hCt hCg hCout hCin

end Oberwolfach
