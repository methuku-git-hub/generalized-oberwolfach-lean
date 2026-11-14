module

public import Oberwolfach.MarkedFreshEndpointBlocks
public import Oberwolfach.MarkedEndpointColumnEstimates
public import Oberwolfach.MappedFactorGraph

@[expose] public section

/-! The fresh endpoint block hypotheses are derived from the marked row
and index profiles. Errors retain their original domains. The exceptional
pairs are precisely those at permutation distance at most 3d. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fresh_endpoint_profiles (p₀ a ε:ℝ)
    (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1) (hε:0<ε):
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (d q:ℕ) (ρ:ℝ) (hρ:0<ρ) (hρ1:ρ≤1),∃ N:ℕ,
    ∀ (V U Γ Color J:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      [Fintype Γ] [Fintype Color] [Fintype J],
      N≤Fintype.card (V⊕U)→Fintype.card J≤(Fintype.card (V⊕U))^2→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (h:ℕ) (A:Finset V) (B:Finset U)
      (p k:ℝ) (q₀:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j₀:Color)
      (errR errI:ℝ) (σ₀:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
      (w:Bool→ℝ) (mark incoming r t:J→Bool) (root:J→V),
      3≤h→0≤errR→0≤errI→
      2*errR≤η*(a*Fintype.card (V⊕U))→2*errI≤η*(a*Fintype.card (V⊕U))→
      MarkedRowsWithSpokes P π d h A p k q₀ s g j₀ errR σ₀ H→
      MarkedIndicesWithSpokes π d h B q₀ s g j₀ errI σ₀ H→
      (∀ u∈B,q₀ u g=w true)→(∀ u∈B,s u j₀=w false)→
      (∀ e,p₀≤w e ∧ w e≤1)→
    let L:=fun j=>markedEndpointLabels P π d A (mark j,incoming j,root j) σ₀;
    let Y:=fun j=>B.filter (H (r j) (root j));
      (∀ j,a*Fintype.card (V⊕U)≤((L j).card:ℝ) ∧ a*Fintype.card (V⊕U)≤((Y j).card:ℝ))→
      1-1/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin ρ hρ.le hρ1)).probability
        (fun σ=>∀ j (A':Finset V) (B':Finset U) (D:SimpleGraph (V⊕U)),A'⊆L j→B'⊆Y j→
          ((changed A' ((L j).filter (fun v=>σ (markedBoundaryEndpointCoin π (mark j) (incoming j) (root j) (Sum.inl v))=true))).card:ℝ)≤ζ*(ρ*Fintype.card (V⊕U))→
          ((changed B' ((Y j).filter (fun u=>σ s(Sum.inl (root j),Sum.inr u)=true))).card:ℝ)≤ζ*(ρ*Fintype.card (V⊕U))→
          (∀ z,(D.degree z:ℝ)≤ζ*(ρ*Fintype.card (V⊕U)))→
          ρ*(L j).card/2≤(A'.card:ℝ) ∧ ρ*(Y j).card/2≤(B'.card:ℝ) ∧
          ∀ degree tau:ℝ,degree≤p₀/2*A'.card→degree≤p₀/2*B'.card→ε*A'.card≤tau→ε*B'.card≤tau→
          BipartiteBlockBounds (fun v u=>H (t j) v u∧¬D.Adj (Sum.inl v) (Sum.inr u))
            (fun v=>v∈A') (fun u=>u∈B') degree tau (p₀/2)) := by
  obtain ⟨η,ζ,hη,hζ,hbase⟩:=marked_fresh_endpoint_blocks p₀ a ε hp₀ hp₀1 ha ha1 hε
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro d q ρ hρ hρ1
  obtain ⟨N,hN⟩:=hbase (6*d) q ρ hρ hρ1
  refine ⟨N,?_⟩
  intro V U Γ Color J _ _ _ _ _ _ _ hn hJ P π h A B p k q₀ s g j₀
    errR errI σ₀ H w mark incoming r t root hh hR hI heR heI hr hi hq hs hw L Y hsize
  let F:SimpleGraph (V⊕U):=(permutationConflictGraph π (3*d)).map (Sum.inl:V→V⊕U)
  have hF (z:V⊕U):F.degree z≤6*d:=by
    convert graph_map_degree_bound (permutationConflictGraph π (3*d))
      ⟨Sum.inl,Sum.inl_injective⟩ (6*d) (fun v=>by
        convert permutationConflictGraph_degree_le π (3*d) v using 1 <;> omega) z using 1 <;> congr!
  have herrR (j:J):2*errR≤η*(L j).card:=
    heR.trans (mul_le_mul_of_nonneg_left (hsize j).1 hη.le)
  have herrI (j:J):2*errI≤η*(Y j).card:=
    heI.trans (mul_le_mul_of_nonneg_left (hsize j).2 hη.le)
  have hwi (e:Bool):0≤w e ∧ w e≤1:=⟨hp₀.le.trans (hw e).1,(hw e).2⟩
  apply hN V U J hn hJ π mark incoming root (fun j=>H (t j)) (fun _=>F) L Y (fun j=>w (t j))
    (fun j=>hw (t j)) hsize (by intro j z;convert hF z using 1 <;> congr!)
  · intro j v hv
    have hvsep:=marked_endpoint_labels_separated P π d A (mark j,incoming j,root j) σ₀ v hv
    exact ((marked_endpoint_index_estimates π d h hh B q₀ s g j₀ errI hI σ₀ H hi w hq hs hwi
      (r j) (t j) (root j)).2.1 v hvsep).trans (herrI j)
  · intro j u hu
    have huB:= (Finset.mem_filter.mp hu).1
    exact ((marked_endpoint_column_estimates P π d h (by omega) A B p k q₀ s g j₀ errR hR
      σ₀ H hr w hq hs hwi (mark j,incoming j,root j)).2 (t j) u huB).trans (herrR j)
  · intro j v hv z hz hne hFvz
    have hsep:¬PermutationClose π (3*d) v z:=by
      intro hc
      apply hFvz
      change ((permutationConflictGraph π (3*d)).map (Sum.inl:V→V⊕U)).Adj _ _
      rw [SimpleGraph.map_adj' ]
      exact ⟨fun he=>hne (Sum.inl.inj he),v,z,⟨hne,hc⟩,rfl,rfl⟩
    have hvsep:=marked_endpoint_labels_separated P π d A (mark j,incoming j,root j) σ₀ v hv
    have hzsep:=marked_endpoint_labels_separated P π d A (mark j,incoming j,root j) σ₀ z hz
    have he:=(marked_endpoint_index_estimates π d h hh B q₀ s g j₀ errI hI σ₀ H hi w hq hs hwi
      (r j) (t j) (root j)).2.2 v z hvsep hzsep hsep
    change (((Y j).filter (fun u=>H (t j) v u∧H (t j) z u)).card:ℝ)≤w (t j)^2*(Y j).card+2*errI at he
    nlinarith only [he,herrI j]

end Oberwolfach
