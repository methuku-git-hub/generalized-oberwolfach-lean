module

public import Oberwolfach.OrdinaryRowRootCover
public import Oberwolfach.RootCoverDeletionCounts
public import Oberwolfach.WheelFamilyReindex

@[expose] public section

/-! The row-root cover under a later bounded deletion. All count and cut
hypotheses are on the original host; no post-deletion factor or pairing
is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_row_root_after_deletion (lam:ℝ) (hlam:0<lam) :
    ∀ d:ℕ,∃ N:ℕ,∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      ∀ (Q F:SimpleGraph V) (H:V→U→Prop) (r K:ℕ),4≤r → 0<K →
      ∀ (x:V) (A:Finset V),x∉A → Q.neighborFinset x⊆A →
      ∀ b L:ℝ,
      let T:=Finset.univ.filter (H x)
      N≤T.card → Q.degree x=2*T.card →
      (∀ a,F.degree a≤d) → (∀ a,Q.Adj x a → ¬F.Adj x a) →
      (∀ a,Q.Adj x a → 2*lam*T.card≤((T.filter (H a)).card:ℝ)) →
      (∀ u∈T,4*lam*T.card≤(((Q.neighborFinset x).filter (fun a=>H a u)).card:ℝ)) →
      (∀ S⊆Q.neighborFinset x,∀ J⊆T,lam/16*T.card≤(S.card:ℝ) → lam/16*T.card≤(J.card:ℝ) →
        2*lam*S.card*J.card≤(bipartiteMatrixCut (fun a u=>if H a u then 1 else 0) S J:ℝ)) →
      (∀ u∈T,∀ a,a≠x → ∀ c,c≠x →
        b≤(((A.filter (fun z=>H z u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)) →
      0≤L → L≤lam*T.card → L≤lam^2*T.card/16 →
      (T.card*r:ℕ)/(K:ℝ)+((r:ℝ)+3)*(d+1)+4*(K+1)+3*L<b →
      ∀ (D:SimpleGraph V) (E:V→U→Prop),
      (∀ a,(D.degree a:ℝ)≤L) →
      (∀ a,((Finset.univ.filter (E a)).card:ℝ)≤L) →
      (∀ u,((Finset.univ.filter (fun a=>E a u)).card:ℝ)≤L) →
      (∀ a,¬D.Adj x a) → (∀ u,¬E x u) →
      ∃ C:Fin T.card→OrdinaryWheel (Q\D) F (fun a u=>H a u∧¬E a u) r,
        (∀ i,∀ a∈(ordinaryWheelRim (C i)).support,a=x∨a∈A) ∧
        (∀ i,H x (ordinaryWheelHub (C i))) ∧
        (∀ i j,i≠j → Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
        (∀ a,(wheelFamilyRim C).Adj x a ↔ Q.Adj x a) ∧
        (∀ u,wheelFamilySpokes C x u ↔ H x u) ∧
        (∀ a,a≠x → (wheelFamilyRim C).degree a≤2*(K+1)) ∧
        (∀ a,a≠x → (Finset.univ.filter (fun u=>wheelFamilySpokes C a u)).card≤K+1) ∧
        (∀ u,(Finset.univ.filter (fun a=>wheelFamilySpokes C a u)).card≤r) := by
  intro d
  obtain ⟨N,hN⟩:=ordinary_row_root_cover lam hlam d
  refine ⟨N,?_⟩
  intro V U _ _ _ _ Q F H r K hr hK x A hxA hSA b L T hn hbal hF hFx hrow hcol hcut hcount hL hLrow hLcut hbudget D E hD hErow hEcol hxD hxE
  have hroot (a:V):(Q\D).Adj x a ↔ Q.Adj x a:=by simp only [SimpleGraph.sdiff_adj,hxD a,not_false_eq_true,and_true]
  have hneigh:(Q\D).neighborFinset x=Q.neighborFinset x:=by ext a;simp only [SimpleGraph.mem_neighborFinset,hroot]
  have hT:(Finset.univ.filter (fun u=>H x u∧¬E x u))=T:=by
    ext u;simp only [T,Finset.mem_filter,Finset.mem_univ,true_and,hxE u,not_false_eq_true,and_true]
  have hdeg:(Q\D).degree x=2*T.card:=by rw [←SimpleGraph.card_neighborFinset_eq_degree,hneigh,SimpleGraph.card_neighborFinset_eq_degree,hbal]
  have hrow' (a:V) (ha:Q.Adj x a):lam*T.card≤((T.filter (fun u=>H a u∧¬E a u)).card:ℝ):=by
    have hh:=finite_domain_filter_deleted T (H a) (E a)
    have hh':((T.filter (H a)).card:ℝ)≤(T.filter (fun u=>H a u∧¬E a u)).card+(Finset.univ.filter (E a)).card:=by exact_mod_cast hh
    linarith only [hh',hrow a ha,hErow a,hLrow]
  have hcol' (u:U) (hu:u∈T):2*lam*T.card≤(((Q.neighborFinset x).filter (fun a=>H a u∧¬E a u)).card:ℝ):=by
    have hh:=finite_domain_filter_deleted (Q.neighborFinset x) (fun a=>H a u) (fun a=>E a u)
    have hh':(((Q.neighborFinset x).filter (fun a=>H a u)).card:ℝ)≤
      ((Q.neighborFinset x).filter (fun a=>H a u∧¬E a u)).card+(Finset.univ.filter (fun a=>E a u)).card:=by exact_mod_cast hh
    linarith only [hh',hcol u hu,hEcol u,hLrow,hL]
  have hcut' (S:Finset V) (hS:S⊆Q.neighborFinset x) (J:Finset U) (hJ:J⊆T)
      (hs:lam/16*T.card≤(S.card:ℝ)) (hj:lam/16*T.card≤(J.card:ℝ)) :
      lam*S.card*J.card≤(bipartiteMatrixCut (fun a u=>if H a u∧¬E a u then 1 else 0) S J:ℝ):=by
    have hh:=bipartite_cut_deleted_column H E L hEcol S J
    have hls:L≤lam*S.card:=by nlinarith only [hLcut,mul_le_mul_of_nonneg_left hs hlam.le]
    have hloss:=mul_le_mul_of_nonneg_right hls (Nat.cast_nonneg J.card : (0:ℝ)≤J.card)
    have hc:=hcut S hS J hJ hs hj
    nlinarith only [hh,hloss,hc]
  have hcount' (u:U) (hu:u∈T) (a:V) (ha:a≠x) (c:V) (hc:c≠x) :
      b-3*L≤(((A.filter (fun z=>H z u∧¬E z u))∩(Q\D).neighborFinset a∩(Q\D).neighborFinset c).card:ℝ):=by
    have hh:=two_rim_one_spoke_deleted Q D H E A a c u
    have hh':(((A.filter (fun z=>H z u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)≤
      ((A.filter (fun z=>H z u∧¬E z u))∩(Q\D).neighborFinset a∩(Q\D).neighborFinset c).card+
        D.degree a+D.degree c+(Finset.univ.filter (fun z=>E z u)).card:=by exact_mod_cast hh
    linarith only [hh',hcount u hu a ha c hc,hD a,hD c,hEcol u]
  have hcolnew (u:U) (hu:u∈T):2*lam*T.card≤(((Q\D).neighborFinset x).filter (fun a=>H a u∧¬E a u)).card:=by
    have he:((Q\D).neighborFinset x).filter (fun a=>H a u∧¬E a u)=
        (Q.neighborFinset x).filter (fun a=>H a u∧¬E a u):=by
      ext a;simp only [Finset.mem_filter,SimpleGraph.mem_neighborFinset,hroot]
    rw [he];exact hcol' u hu
  have hcutnew (S:Finset V) (hS:S⊆(Q\D).neighborFinset x) (J:Finset U) (hJ:J⊆T)
      (hs:lam/16*T.card≤(S.card:ℝ)) (hj:lam/16*T.card≤(J.card:ℝ)) :
      lam*S.card*J.card≤(bipartiteMatrixCut (fun a u=>if H a u∧¬E a u then 1 else 0) S J:ℝ):=by
    apply hcut' S _ J hJ hs hj
    intro a ha
    exact (Q.mem_neighborFinset x a).mpr ((hroot a).mp (((Q\D).mem_neighborFinset x a).mp (hS ha)))
  have hHx:(fun u=>H x u∧¬E x u)=H x:=by funext u;apply propext;simp [hxE]
  have happly:=@hN V U inferInstance inferInstance inferInstance inferInstance
    (Q\D) F (fun a u=>H a u∧¬E a u) r K hr hK x A hxA
    (by convert hSA using 1; ext a;simp only [SimpleGraph.mem_neighborFinset,hroot]) (b-3*L)
  dsimp only at happly
  simp_rw [hHx] at happly
  have hresult:=happly
    (by convert hn using 1 <;> congr!)
    (by convert hdeg using 1 <;> congr!) hF
    (fun a ha=>hFx a ((hroot a).mp ha))
    (by convert hrow' using 1 <;> simp only [hroot] <;> congr!)
    (by convert hcolnew using 1 <;> congr!)
    (by
      intro S hS J hJ hs hj
      have hS' : S ⊆ (Q\D).neighborFinset x := by
        intro a ha
        have h := hS ha
        simpa only [SimpleGraph.mem_neighborFinset] using h
      have hJ' : J ⊆ T := by simpa only [T] using hJ
      have hs' : lam/16*T.card≤(S.card:ℝ) := by simpa only [T] using hs
      have hj' : lam/16*T.card≤(J.card:ℝ) := by simpa only [T] using hj
      have hh := hcutnew S hS' J hJ' hs' hj'
      convert hh using 1 <;> congr!)
    (by convert hcount' using 1 <;> congr!)
    (by convert (show (T.card*r:ℕ)/(K:ℝ)+((r:ℝ)+3)*(d+1)+4*(K+1)<b-3*L from by linarith only [hbudget]) using 1 <;> congr!)
  obtain ⟨C,hCs,hCh,hCd,hCr,hCt,hCg,hCout,hCin⟩:=hresult
  have hTc:(Finset.univ.filter (fun u=>H x u∧¬E x u)).card=T.card:=congrArg Finset.card hT
  let C':Fin T.card→OrdinaryWheel (Q\D) F (fun a u=>H a u∧¬E a u) r:=
    wheelFamilyReindex C (by convert hTc.symm using 1 <;> congr!)
  have hR:wheelFamilyRim C'=wheelFamilyRim C:=wheelFamilyReindex_rim C _
  have hS:wheelFamilySpokes C'=wheelFamilySpokes C:=wheelFamilyReindex_spokes C _
  refine ⟨C',?_,?_,wheelFamilyReindex_disjoint C _ hCd,?_,?_,?_,?_,?_⟩
  · intro i;exact hCs _
  · intro i;exact (hCh _).1
  · intro a;rw [hR];exact (hCr a).trans (hroot a)
  · intro u;rw [hS];exact (hCt u).trans (by simp only [hxE u,not_false_eq_true,and_true])
  · intro a ha;convert hCg a ha using 1;rw [hR]
  · simpa only [hS] using hCout
  · simpa only [hS] using hCin

end Oberwolfach
