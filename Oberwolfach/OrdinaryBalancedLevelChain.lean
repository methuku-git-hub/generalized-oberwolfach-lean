module

public import Oberwolfach.OrdinaryLevelChainCompletion

@[expose] public section
/-! Supply the actual balanced and divisible remainder to each ordinary
level step. Balance is propagated by wheel decompositions on one resource
universe; the analytic level invariant remains an explicit input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_balanced_level_chain_completion
    (Q P F:SimpleGraph V) (H Hbase:V→U→Prop) (r m:ℕ)
    (W:Finset V) (B:Finset U) (hsize:W.card+B.card≤m)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hP:∀v∈W,∀w∈W,Q.Adj v w→P.Adj v w)
    (hH:∀v∈W,∀u∈B,H v u→Hbase v u)
    (A:Finset (Sym2 V⊕(V×U))) (hA:A⊆ordinaryHostResources Q H)
    (hdecA:HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) A)
    (hres:∀(G':SimpleGraph V) (H':V→U→Prop),
      ordinaryHostResources G' H'⊆ordinaryRootResources W B →
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m →
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) →
      G'≤P → (∀v u,H' v u→Hbase v u) →
      IsResourceAbsorber (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r))
        (ordinaryHostResources G' H') A)
    (L:ℕ) (Good:ℕ→Finset (Sym2 V⊕(V×U))→Prop)
    (hInitial:Good 0 (ordinaryHostResources Q H\A))
    (hStep:∀i<L,∀S (G:SimpleGraph V) (Hs:V→U→Prop),
      Good i S → ordinaryHostResources G Hs=S → G≤Q → (∀v u,Hs v u→H v u) →
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card) →
      ∃T,Good (i+1) T ∧ T⊆S ∧
        HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) (S\T))
    (hTerminal:∀T,Good L T→T⊆ordinaryRootResources W B):
    HasOrdinaryWheelDecomposition Q H r:=by
  let Host:=ordinaryHostResources Q H
  let Wheel:=ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)
  let Good':=fun i S=>Good i S ∧ S⊆Host ∧ HasResourceDecomposition Wheel (Host\S)
  have hInitial':Good' 0 (Host\A):=by
    refine ⟨hInitial,Finset.sdiff_subset,?_⟩
    have heq:Host\(Host\A)=A:=by
      ext e
      have ha:=fun he=>hA (x:=e) he
      simp only [Finset.mem_sdiff]
      tauto
    rw [heq]
    exact hdecA
  have hStep':∀i<L,∀S,Good' i S→∃T,Good' (i+1) T ∧ T⊆S ∧ HasResourceDecomposition Wheel (S\T):=by
    intro i hi S ⟨hgood,hsub,hdec⟩
    have hDel:Host\S⊆Host:=Finset.sdiff_subset
    obtain ⟨G,Hs,hEq,hb,hd,hG,hHsub⟩:=ordinary_resource_terminal_remainder_balance
      Q P F H Hbase r hbal hdiv (Host\S) hDel hdec
    have hSS:Host\(Host\S)=S:=by
      ext e
      have hs:=fun he=>hsub (x:=e) he
      simp only [Finset.mem_sdiff]
      tauto
    rw [hSS] at hEq
    obtain ⟨T,hgoodT,hTS,hdecST⟩:=hStep i hi S G Hs hgood hEq hG hHsub hb hd
    have hdis:Disjoint (Host\S) (S\T):=by
      apply Finset.disjoint_left.mpr
      intro e he he'
      exact (Finset.mem_sdiff.mp he).2 (Finset.mem_sdiff.mp he').1
    have hwhole:=resource_decomposition_union Wheel (Host\S) (S\T) hdec hdecST hdis
    have heq:(Host\S)∪(S\T)=Host\T:=by
      ext e
      have hs:=fun he=>hsub (x:=e) he
      have ht:=fun he=>hTS (x:=e) he
      simp only [Finset.mem_union,Finset.mem_sdiff]
      tauto
    rw [heq] at hwhole
    exact ⟨T,⟨hgoodT,hTS.trans hsub,hwhole⟩,hTS,hdecST⟩
  exact ordinary_level_chain_reservoir_completion Q P F H Hbase r m W B hsize hbal hdiv hP hH A hA hdecA hres
    L Good' hInitial' hStep' (fun T h=>hTerminal T h.1)
end Oberwolfach
