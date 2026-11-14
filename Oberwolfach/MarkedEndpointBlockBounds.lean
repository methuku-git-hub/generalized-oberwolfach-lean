module

public import Oberwolfach.MarkedEndpointColumnEstimates
public import Oberwolfach.BipartiteBlockFromCodegrees

@[expose] public section

/-! The actual one-arc row and typed index estimates imply the degree
and cut assumptions for each of the five marked endpoint blocks. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_endpoint_block_bounds
    (P : SimpleGraph V) (π : Equiv.Perm V) (d h : ℕ) (hh : 3≤h) (A : Finset V) (B : Finset U)
    (p k : ℝ) (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color)
    (errR errI e eta degree tau lam : ℝ) (hR : 0≤errR) (hI : 0≤errI)
    (he : 0≤e) (heta : 0<eta)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hr : MarkedRowsWithSpokes P π d h A p k q s g j errR σ H)
    (hi : MarkedIndicesWithSpokes π d h B q s g j errI σ H)
    (w : Bool→ℝ) (hq : ∀ u∈B,q u g=w true) (hs : ∀ u∈B,s u j=w false)
    (hw : ∀ t,0<w t ∧ w t≤1) (a : Bool×Bool×V) (r t : Bool)
    (hY : 0<(B.filter (H r a.2.2)).card)
    (hrelR : 2*errR≤e*(markedEndpointLabels P π d A a σ).card)
    (hrelI : 2*errI≤e*(B.filter (H r a.2.2)).card)
    (hsmall : e≤(w t)^2*eta/24)
    (hlarge : ((6*d+1:ℕ):ℝ)≤(w t)^2*eta^2*(B.filter (H r a.2.2)).card/8)
    (hdY : degree≤(w t-e)*(B.filter (H r a.2.2)).card)
    (hdL : degree≤(w t-e)*(markedEndpointLabels P π d A a σ).card)
    (htau : eta*(B.filter (H r a.2.2)).card≤tau) (hlam : lam≤w t/2) :
    BipartiteBlockBounds (H t) (fun z=>z∈markedEndpointLabels P π d A a σ)
      (fun u=>u∈B.filter (H r a.2.2)) degree tau lam := by
  let L := markedEndpointLabels P π d A a σ
  let Y := B.filter (H r a.2.2)
  have hix := marked_endpoint_index_estimates π d h hh B q s g j errI hI σ H hi
    w hq hs (fun t=>⟨(hw t).1.le,(hw t).2⟩) r t a.2.2
  have hco := marked_endpoint_column_estimates P π d h (by omega) A B p k q s g j errR hR
    σ H hr w hq hs (fun t=>⟨(hw t).1.le,(hw t).2⟩) a
  have hycard : (Finset.univ.filter (fun u=>u∈Y))=Y := by ext u;simp
  have hlcard : (Finset.univ.filter (fun z=>z∈L))=L := by ext z;simp
  apply bipartite_block_bounds_of_codegrees (H t) (fun z=>z∈L) (fun u=>u∈Y)
    (permutationConflictGraph π (3*d)) (6*d) (w t) e eta degree tau lam
    (hw t).1 (hw t).2 he heta
    (by simpa only [Finset.filter_mem_eq_inter,Finset.univ_inter] using hY)
    (by intro z;convert permutationConflictGraph_degree_le π (3*d) z using 1 <;> omega)
  · intro z hz
    have hh := (abs_le.mp (hix.2.1 z (marked_endpoint_labels_separated P π d A a σ z hz))).1
    have hset : (Finset.univ.filter (fun u=>u∈Y ∧ H t z u))=Y.filter (H t z) := by ext u;simp
    simp only [←Finset.filter_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
    change -(2*errI)≤((Y.filter (H t z)).card:ℝ)-w t*Y.card at hh
    change 2*errI≤e*Y.card at hrelI
    nlinarith only [hh,hrelI]
  · intro u hu
    have huB : u∈B := (Finset.mem_filter.mp hu).1
    have hh := (abs_le.mp (hco.2 t u huB)).1
    have hset : (Finset.univ.filter (fun z=>z∈L ∧ H t z u))=L.filter (fun z=>H t z u) := by ext z;simp
    simp only [←Finset.filter_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
    change 2*errR≤e*L.card at hrelR
    change -(2*errR)≤((L.filter (fun z=>H t z u)).card:ℝ)-w t*L.card at hh
    nlinarith only [hh,hrelR]
  · intro z hz z' hz' hne hbad
    have hclose : ¬PermutationClose π (3*d) z z' := fun hc=>hbad ⟨hne,hc⟩
    have hh := hix.2.2 z z' (marked_endpoint_labels_separated P π d A a σ z hz)
      (marked_endpoint_labels_separated P π d A a σ z' hz') hclose
    have hset : (Finset.univ.filter (fun u=>u∈Y ∧ H t z u ∧ H t z' u))=
        Y.filter (fun u=>H t z u ∧ H t z' u) := by ext u;simp
    simp only [←Finset.filter_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
    simp only [Finset.filter_filter]
    change ((Y.filter (fun u=>H t z u ∧ H t z' u)).card:ℝ)≤(w t)^2*Y.card+2*errI at hh
    change 2*errI≤e*Y.card at hrelI
    nlinarith only [hh,hrelI]
  · exact hsmall
  · simpa only [Finset.filter_mem_eq_inter,Finset.univ_inter,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] using hlarge
  · simpa only [Finset.filter_mem_eq_inter,Finset.univ_inter] using hdY
  · simpa only [Finset.filter_mem_eq_inter,Finset.univ_inter] using hdL
  · simpa only [Finset.filter_mem_eq_inter,Finset.univ_inter] using htau
  · exact hlam

end Oberwolfach
