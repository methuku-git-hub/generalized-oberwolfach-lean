module

public import Oberwolfach.MarkedPrescribedSubgraphPacking
public import Oberwolfach.MarkedSampledHostCounts
public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion

@[expose] public section

/-! The prescribed inner-edge packing in an actual retained sample after
physical deletion. Its extension counts are derived from the original
fixed neighbourhood profiles, uniformly for every permitted deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sample_prescribed_packing_after_deletion
    (l:ℕ) (hl:2≤l) (pstar gamma omega:ℝ)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hg:0<gamma) (hg1:gamma≤1) (ho:0<omega):
    ∃ beta eps delta eta₀:ℝ,0<beta ∧ 0<eps ∧ 0<delta ∧ 0<eta₀ ∧
    ∀ eta:ℝ,0<eta→eta≤eta₀→∀ d:ℕ,1≤d→∃ N:ℕ,1≤N ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→ omega*Fintype.card V≤(Fintype.card U:ℝ)→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),
    (∀ x,(1/2+gamma/2)*Fintype.card V≤(P.degree x:ℝ))→
    ∀ (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color),
    pstar≤p→pstar≤k→(∀ u,pstar≤q u g)→(∀ u,pstar≤s u j)→
    ∀ (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop),
    MarkedRowsWithSpokes P π d (l+12) Finset.univ p k q s g j (eps*Fintype.card V) σ H→
    MarkedIndicesWithSpokes π d (l+12) Finset.univ q s g j (eps*Fintype.card V) σ H→
    ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
    (∀ x,(DR.degree x:ℝ)≤delta*Fintype.card V)→
    (∀ x,(DS.degree (Sum.inl x):ℝ)≤delta*Fintype.card V)→
    (∀ u,(DS.degree (Sum.inr u):ℝ)≤delta*Fintype.card V)→
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    ∀ (X:Finset V) (J:Finset U),(∀ x,π x∈X↔x∈X)→
    ((Xᶜ).card:ℝ)≤beta*Fintype.card V/10→(J.card:ℝ)≤beta*Fintype.card V/10→
    ∀ (A:Finset (E₀⊕E₁)) (S:Finset (V×U)),
    (A.card:ℝ)≤eta^2*(Fintype.card V:ℝ)^2→(S.card:ℝ)≤eta^2*(Fintype.card V:ℝ)^2→
    (∀ a∈A,Sum.elim tail ktail a∉X∧Sum.elim head khead a∉X)→
    (∀ v,((A.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤eta^2*Fintype.card V)→
    (∀ z∈S,z.1∉X∧z.2∈J∧(H' false z.1 z.2∨H' true z.1 z.2))→
    (∀ v,((S.filter (fun z=>v=z.1)).card:ℝ)≤eta^2*Fintype.card V)→
    (∀ u,((S.filter (fun z=>z.2=u)).card:ℝ)≤eta^2*Fintype.card V)→
    ∃ M:Finset (MarkedWheel tail head ktail khead (l+4) π (3*d) (H' false) (H' true)),
      (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource (Xᶜ) J)=
        A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr∧
      (∀ v,((markedPackingRimGraph M).degree v:ℝ)≤24*eta*Fintype.card V)∧
      (∀ v,((Finset.univ.filter (markedPackingSpokes M v)).card:ℝ)≤6*eta*Fintype.card V)∧
      (∀ u,((Finset.univ.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤3*(l+5)*eta*Fintype.card V):=by
  let beta:=min (pstar^4*gamma/4) (pstar^(l+12)*omega/2)
  let eext:=min (pstar^4*gamma/4) (pstar^(l+12)/2)
  have hb:0<beta:=by dsimp [beta];positivity
  have hext:0<eext:=by dsimp [eext];positivity
  let scale:=min 1 omega
  have hscale:0<scale:=lt_min zero_lt_one ho
  let eps:=eext*scale/2
  let delta:=eext*scale/(8*(l+12:ℕ))
  have heps:0<eps:=by dsimp [eps];positivity
  have hdelta:0<delta:=by dsimp [delta];positivity
  obtain ⟨eta₀,heta₀,hpack⟩:=marked_sparse_prescribed_subgraph_packing l hl beta hb
  refine ⟨beta,eps,delta,eta₀,hb,heps,hdelta,heta₀,?_⟩
  intro eta heta hetasmall d hd
  obtain ⟨N₀,hpack⟩:=hpack eta heta hetasmall (3*d) (by omega)
  obtain ⟨N₁,hN₁⟩:=exists_nat_gt (4*(6*(d:ℝ)+1)/gamma)
  refine ⟨max 1 (max N₀ N₁),le_max_left _ _,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hU P π hdeg p k q s g j hp hk hq hs σ H hr hi DR DS hDR hDSv hDSu
  dsimp only
  intro X J hX hXI hJ A S hAcard hScard hArows hAdeg hS hSrow hScol
  let n:=Fintype.card V
  have hn0:(0:ℝ)≤n:=Nat.cast_nonneg n
  have hhpos:(0:ℝ)<(l+12:ℕ):=by positivity
  have hdlt:(l+12:ℕ)*delta=eext*scale/8:=by
    dsimp only [delta]
    field_simp
  have hscale1:scale≤1:=min_le_left _ _
  have hscaleo:scale≤omega:=min_le_right _ _
  have hrowErr:eps*n+(l+12:ℕ)*(delta*n+delta*n)≤eext*n:=by
    have hh:=mul_le_mul_of_nonneg_left hscale1 hext.le
    dsimp only [eps]
    nlinarith only [hdlt,hh,hext,hn0,hdelta,heps]
  have hidxErr:eps*n+(l+12:ℕ)*(delta*n)≤eext*Fintype.card U:=by
    have hh:=mul_le_mul_of_nonneg_left hscaleo hext.le
    have hu:=mul_le_mul_of_nonneg_left hU hext.le
    dsimp only [eps,n] at *
    nlinarith only [hdlt,hh,hu,hext,hn0,hdelta,heps]
  obtain ⟨hr',hi'⟩:=marked_neighbourhoods_after_physical_deletion P π d (l+12) Finset.univ Finset.univ
    p k q s g j (eps*n) (eps*n) (delta*n) (delta*n) (delta*n)
    (mul_nonneg hdelta.le hn0) (mul_nonneg hdelta.le hn0) (mul_nonneg hdelta.le hn0)
    σ H hr hi DR DS hDR hDSv hDSu
  have hrows:MarkedRowsWithSpokes P π d (l+1+11) Finset.univ p k q s g j (eext*n)
      (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS):=by
    intro R T I hR hT hI hinj
    exact (hr' R T I hR hT hI hinj).trans_le hrowErr
  have hindices:MarkedIndicesWithSpokes π d (l+1+11) Finset.univ q s g j (eext*Fintype.card U)
      (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS):=by
    intro I hI hsep
    exact (hi' I hI hsep).trans_le hidxErr
  have hloss:2*(2*(3*d:ℕ)+1:ℝ)≤gamma*n/2:=by
    have hnd:N₁≤n:=(le_max_right _ _).trans ((le_max_right _ _).trans hn)
    have hh:4*(6*(d:ℝ)+1)<(n:ℝ)*gamma:=
      (div_lt_iff₀ hg).mp (hN₁.trans_le (Nat.cast_le.mpr hnd))
    push_cast
    linarith only [hh]
  have Q:=marked_sampled_host_extension_counts P π d (l+1) p k q s g j eext gamma pstar omega
    hpstar hpstar1 hg hg1 hp hk hq hs (min_le_left _ _) (min_le_right _ _) hloss hdeg hU
    (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS) hrows hindices
  have Q':=Q.lowerBounds (c':=beta*n) (h':=beta*n) (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0)
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hn0)
  apply hpack V U _ _ _ _ _ _ _ _ π ((le_max_left _ _).trans ((le_max_right _ _).trans hn))
    Q' (markedSampleArc_physical_injective P π (3*d) _) X J hX hXI hJ A S hAcard hScard hArows
      _ hAdeg hS hSrow hScol
  intro a _
  cases a with
  | inl a=>exact (markedPhysicalRim_eq_one_iff P π (3*d) _ _ _ _).mp a.property |>.1
  | inr a=>exact (markedPhysicalRim_eq_one_iff P π (3*d) _ _ _ _).mp a.property |>.1

end Oberwolfach
