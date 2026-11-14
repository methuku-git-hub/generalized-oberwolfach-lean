module

public import Oberwolfach.FactorSmallClassBudget
public import Oberwolfach.FactorSmallClassFromDecompositions

@[expose] public section
/-! The class-size cutoffs, deletion budget and density-one decomposition
input combine to remove the actual small-class factors in a fixed order. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_pruned_family_removal {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
    (K:ℕ) (hK:0<K) (classify:W→Option (Fin K))
    (D:ℕ) (δ α κL κS:ℝ) (hδ:0≤δ) (hα:0<α)
    (hL0:0≤κL) (hS0:0≤κS) (hL:κL≤α/1000) (hS:κS≤α/(1000*(K:ℝ)))
    (G:SimpleGraph (Fin n)) (hG:G.IsRegularOfDegree D) (hEven:Even D)
    (hdegree:(δ+α)*(n:ℝ)≤D) (F:W→SimpleGraph (Fin n))
    (hF:∀ w,(F w).IsRegularOfDegree 2):
    let fibres:=fun j:Option (Fin K)=>Finset.univ.filter (fun w=>classify w=j)
    let small:=fun j:Option (Fin K)=>
      ((fibres j).card:ℝ)<(if j=none then κL*n else κS*n)
    let removed:=Finset.univ.filter (fun w=>small (classify w))
    let list:=removed.toList.map F;
    (∀ P:SimpleGraph (Fin n),∀ d:ℕ,P.IsRegularOfDegree d→Even d→
      (δ+α/2)*(n:ℝ)≤d→∀ w∈removed,
      HasFactorDecomposition P (fun _:Fin (d/2)=>F w))→
    ∃ R:SimpleGraph (Fin n),∃ pieces:List (SimpleGraph (Fin n)),
      R.IsRegularOfDegree (D-2*removed.card) ∧ R≤G ∧
      (δ+α/2)*(n:ℝ)≤((D-2*removed.card:ℕ):ℝ) ∧
      List.Forall₂ (fun H A=>Nonempty (H ≃g A) ∧ H.IsRegularOfDegree 2) pieces list ∧
      (∀ H∈pieces,H≤G ∧ ∀ u v,H.Adj u v→¬R.Adj u v) ∧
      pieces.Pairwise (fun H J=>∀ u v,H.Adj u v→¬J.Adj u v) ∧
      (∀ u v,G.Adj u v ↔ R.Adj u v ∨ ∃ H∈pieces,H.Adj u v):=by
  intro fibres small removed list hdecomp
  have hb:=factor_small_class_budget K hK classify (n:ℝ) α κL κS (by positivity) hα hL0 hS0 hL hS
  have hb':(removed.card:ℝ)≤α*n/500:=by simpa [fibres,small,removed] using hb
  have hlen:list.length=removed.card:=by simp [list]
  have hsmall:(list.length:ℝ)≤α*n/500:=by rw [hlen];exact hb'
  have hlist:∀ A∈list,A.IsRegularOfDegree 2:=by
    intro A hA
    obtain ⟨w,_,rfl⟩:=List.mem_map.mp hA
    exact hF w
  have hdec:∀ P:SimpleGraph (Fin n),∀ d:ℕ,P.IsRegularOfDegree d→Even d→
      (δ+α/2)*(n:ℝ)≤d→∀ A∈list,HasFactorDecomposition P (fun _:Fin (d/2)=>A):=by
    intro P d hp he hd A hA
    obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hA
    exact hdecomp P d hp he hd w (by simpa using hw)
  have hh:=factor_small_class_from_decompositions hn D δ α hδ hα G hG hEven hdegree list hlist hsmall hdec
  simpa [hlen] using hh
end Oberwolfach
