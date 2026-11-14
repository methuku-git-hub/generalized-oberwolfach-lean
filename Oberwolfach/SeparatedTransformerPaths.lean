module

public import Oberwolfach.FiniteConflictSeparatedChoices
public import Oberwolfach.TransformerRimPaths

@[expose] public section

/-! Simultaneous construction of the rim paths in a bounded ordinary
transformer. The forbidden set is enlarged by the actual earlier path
supports, whose total size is bounded before each application. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

 theorem separated_transformer_paths (Q F:SimpleGraph V)
    (A:I→Finset V) (W Ω:Finset V) (Z:I→Finset V) (hAΩ:∀ i,A i⊆Ω)
    (x y x' y':I→V) (hroots:∀ i,x i∈Z i∧y i∈Z i∧x' i∈Z i∧y' i∈Z i)
    (hΩ:∀ i,x i∈Ω∧y i∈Ω∧x' i∈Ω∧y' i∈Ω)
    (hZ:∀ i,∀ v∈Z i,∀ w∈Z i,¬F.Adj v w)
    (r:I→ℕ) (d:ℕ) (hr:∀ i,4≤r i) (hd:∀ i,r i-2≤d) (L b:ℝ) (hL:0≤L) (hF:∀ v,(F.degree v:ℝ)≤L)
    (hcount:∀ i,∀ v∈Ω,∀ w∈Ω,b≤((A i∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hthree:∀ i,r i=4→∀ a∈A i,b≤(((A i∩Q.neighborFinset a)∩Q.neighborFinset (y i)∩Q.neighborFinset (y' i)).card:ℝ))
    (hbudget:∀ i,W.card+Fintype.card I*d*(L+1)+(((Z i).card:ℝ)+r i+2)*(L+1)<b):
    ∃ p:I→(Σ a:V,Σ c:V,Q.Walk a c),
      (∀ i,(p i).2.2.IsPath ∧ (p i).2.2.length=r i-3 ∧
        Q.Adj (x i) (p i).1 ∧ Q.Adj (x' i) (p i).1 ∧
        Q.Adj (y i) (p i).2.1 ∧ Q.Adj (y' i) (p i).2.1 ∧
        (∀ v∈(p i).2.2.support,v∈A i∧v∉W∧v∉Z i) ∧
        (∀ v∈(p i).2.2.support,∀ w∈(p i).2.2.support,¬F.Adj v w) ∧
        (∀ v∈(p i).2.2.support,∀ w∈Z i,¬F.Adj v w)) ∧
      ∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset ∧
        (∀ v∈(p i).2.2.support,∀ w∈(p j).2.2.support,¬F.Adj v w):=by
  let S:(Σ a:V,Σ c:V,Q.Walk a c)→Finset V:=fun p=>p.2.2.support.toFinset
  let Good:=fun (i:I) (p:Σ a:V,Σ c:V,Q.Walk a c)=>
    p.2.2.IsPath ∧ p.2.2.length=r i-3 ∧ Q.Adj (x i) p.1 ∧ Q.Adj (x' i) p.1 ∧
      Q.Adj (y i) p.2.1 ∧ Q.Adj (y' i) p.2.1 ∧
      (∀ v∈p.2.2.support,v∈A i∧v∉Z i) ∧
      (∀ v∈p.2.2.support,∀ w∈p.2.2.support,¬F.Adj v w) ∧
      (∀ v∈p.2.2.support,∀ w∈Z i,¬F.Adj v w)
  have hchoose:∀ i,∀ B:Finset V,(B.card:ℝ)≤W.card+Fintype.card I*d*(L+1)→
      ∃ p,Good i p ∧ (S p).card≤d ∧ Disjoint (S p) B:=by
    intro i B hB
    obtain ⟨a,c,p,hp,hlen,hxa,hx'a,hyc,hy'c,hclass,hind,hroot⟩:=
      transformer_rim_common_path Q F (A i) B Ω (Z i) (hAΩ i) (x i) (y i) (x' i) (y' i)
        (hroots i) (hΩ i) (hZ i) (r i) (hr i) L b hL hF (hcount i) (hthree i)
        (by linarith only [hB,hbudget i])
    refine ⟨⟨a,c,p⟩,⟨hp,hlen,hxa,hx'a,hyc,hy'c,?_,hind,hroot⟩,?_,?_⟩
    · intro v hv;exact ⟨(hclass v hv).1,(hclass v hv).2.2⟩
    · have hh:=List.toFinset_card_le p.support
      rw [p.length_support,hlen] at hh
      dsimp only [S]
      have hh' := hd i
      have hh'' := hr i
      omega
    · apply Finset.disjoint_left.mpr
      intro v hv hBv
      exact (hclass v (List.mem_toFinset.mp hv)).2.1 hBv
  obtain ⟨p,hp,hdis⟩:=finite_conflict_separated_choices S Good W d F L hL hF hchoose
  refine ⟨p,?_,?_⟩
  rotate_left
  · intro i j hij
    exact ⟨(hdis i j hij).1,fun v hv w hw=>(hdis i j hij).2 v (List.mem_toFinset.mpr hv) w (List.mem_toFinset.mpr hw)⟩
  intro i
  obtain ⟨hi,hcard,hW⟩:=hp i
  rcases hi with ⟨hpath,hlen,hxa,hx'a,hyc,hy'c,hclass,hind,hroot⟩
  refine ⟨hpath,hlen,hxa,hx'a,hyc,hy'c,?_,hind,hroot⟩
  intro v hv
  exact ⟨(hclass v hv).1,fun hw=>Finset.disjoint_left.mp hW (List.mem_toFinset.mpr hv) hw,(hclass v hv).2⟩

end Oberwolfach
