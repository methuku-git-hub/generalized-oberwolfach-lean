module

public import Oberwolfach.MarkedHostExtensionCounts
public import Oberwolfach.SeparatedDirectedPaths

@[expose] public section

/-! Actual row choices and ordinary paths from the marked host's displayed
intersection counts. Forbidden vertices are deleted from the realized sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_candidate_avoiding (C W Z:Finset V)
    (hc:c≤(C.card:ℝ)) (hbudget:(W.card:ℝ)+Z.card*(2*b+1)<c):
    ∃ v∈C,v∉W∧v∉Z∧∀ z∈Z,¬PermutationClose π b v z:=by
  obtain ⟨v,hv,hW,hZ,hF⟩:=candidate_vertex_avoiding (permutationConflictGraph π b) C W Z (2*b) c
    (fun x=>by exact_mod_cast permutationConflictGraph_degree_le π b x) hc hbudget
  refine ⟨v,hv,hW,hZ,?_⟩
  intro z hz hh
  exact hF z hz ⟨fun he=>hZ (he ▸ hz),hh⟩

theorem marked_host_ordinary_path
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (P:Finset U) (hP:P.card≤2) (W Z:Finset V) (a:ℕ) (x y:V)
    (hxy:¬PermutationClose π b x y)
    (hx:markedSpokesTo H₀ HK false P x) (hy:markedSpokesTo H₀ HK false P y)
    (hxW:x∉W) (hyW:y∉W) (hxZ:x∉Z) (hyZ:y∉Z)
    (hxsep:∀ z∈Z,¬PermutationClose π b x z) (hysep:∀ z∈Z,¬PermutationClose π b y z)
    (hbudget:(W.card:ℝ)+(Z.card+a+4)*(2*b+1)<c):
    ∃ p:Fin (a+3)↪V,p 0=x∧p (Fin.last (a+2))=y∧
      (∀ i,markedSpokesTo H₀ HK false P (p i)∧p i∉W∧p i∉Z∧∀ z∈Z,¬PermutationClose π b (p i) z)∧
      (∀ i:Fin (a+2),markedArcPresent tail head ktail khead false (p i.castSucc) (p i.succ))∧
      PermutationSeparated π b p:=by
  let F:=permutationConflictGraph π b
  let A:ℕ→Finset V:=fun _=>Finset.univ.filter (markedSpokesTo H₀ HK false P)
  let D:ℕ→V→V→Prop:=fun _=>markedArcPresent tail head ktail khead false
  have hF:∀ z,(F.degree z:ℝ)≤2*b:=fun z=>by exact_mod_cast permutationConflictGraph_degree_le π b z
  have ho:∀ i<a,∀ v∈A i,c≤(((A (i+1)).filter (D i v)).card:ℝ):=by
    intro i hi v hv
    have he:(A (i+1)).filter (D i v)=Finset.univ.filter (fun z=>
        markedArcPresent tail head ktail khead false v z∧markedSpokesTo H₀ HK false P z):=by
      ext z;simp only [A,D,Finset.mem_filter,Finset.mem_univ,true_and];tauto
    rw [he];exact Q.outgoing false false v P hP
  have hj:∀ v∈A a,v≠y→c≤(((A (a+1)).filter (fun z=>D a v z∧D (a+1) z y)).card:ℝ):=by
    intro v hv hvy
    have he:(A (a+1)).filter (fun z=>D a v z∧D (a+1) z y)=Finset.univ.filter (fun z=>
        markedArcPresent tail head ktail khead false v z∧markedArcPresent tail head ktail khead false z y∧markedSpokesTo H₀ HK false P z):=by
      ext z;simp only [A,D,Finset.mem_filter,Finset.mem_univ,true_and];tauto
    rw [he];exact Q.twoStep false v y P hvy hP
  obtain ⟨p,hp0,hpn,hpa,hpd,hpf⟩:=separated_directed_path F D A W Z (2*b) c (by positivity) hF a x y
    (fun h=>hxy (Or.inl h)) (fun h=>hxy h.2)
    (by simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and] using hx)
    (by simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and] using hy)
    hxW hyW hxZ hyZ (fun z hz h=>hxsep z hz h.2) (fun z hz h=>hysep z hz h.2) ho hj hbudget
  refine ⟨p,hp0,hpn,?_,hpd,?_⟩
  · intro i
    refine ⟨(Finset.mem_filter.mp (hpa i).1).2,(hpa i).2.1,(hpa i).2.2.1,?_⟩
    intro z hz hh
    exact (hpa i).2.2.2 z hz ⟨fun he=>(hpa i).2.2.1 (he ▸ hz),hh⟩
  · intro i j hij hh
    exact hpf i j ⟨fun he=>hij (p.injective he),hh⟩

end Oberwolfach
