module

public import Oberwolfach.RawOrdinarySeedPhysicalResources
public import Oberwolfach.FiniteSequenceSimpleWalk

@[expose] public section
/-! The ordered ordinary rim supplies the closing arc and a directed simple
path using all its rim vertices, in exactly the original cyclic order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cycleNext_injective {n:ℕ}:Function.Injective (@cycleNext n):=by
  intro i j h
  apply Fin.ext
  have hv:=congrArg Fin.val h
  rw [cycleNext_val,cycleNext_val] at hv
  split_ifs at hv <;> omega

theorem ordinary_packed_wheel_directed_path
    {V U:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (b n:ℕ) (hn:2≤n) (W:OrderedOrdinaryWheel (U:=U) π b (n+1))
    (R:V→V→Prop) (hR:∀i:Fin (n+1),R (W.1.val i) (W.1.val (cycleNext i))):
    let start:=W.1.val (cycleNext 0)
    let finish:=W.1.val 0
    ∃q:(SimpleGraph.completeGraph V).Walk start finish,
      q.IsPath ∧ q.length=n ∧
      q.support.toFinset=Finset.univ.image W.1.val ∧
      R finish start ∧
      (∀k,k<q.length→R (q.getVert k) (q.getVert (k+1))):=by
  classical
  intro start finish
  let f:Fin (n+1)↪V:=⟨fun i=>W.1.val (cycleNext i),
    (permutationSeparated_injective π b W.1.val W.1.property).comp cycleNext_injective⟩
  have hnext:∀i:Fin n,cycleNext (cycleNext i.castSucc)=cycleNext i.succ:=by
    intro i
    apply Fin.ext
    simp only [cycleNext_val,Fin.val_castSucc,Fin.val_succ]
    have hi:=i.isLt
    split_ifs <;> omega
  have hf0:f ⟨0,by omega⟩=start:=rfl
  have hfn:f ⟨n,by omega⟩=finish:=by
    dsimp [f,finish]
    have hh:cycleNext (⟨n,by omega⟩:Fin (n+1))=0:=by
      apply Fin.ext
      rw [cycleNext_val]
      simp
    rw [hh]
  have hadj:∀j:Fin n,(SimpleGraph.completeGraph V).Adj (f ⟨j.val,by omega⟩) (f ⟨j.val+1,by omega⟩):=by
    intro j
    simp only [SimpleGraph.completeGraph_eq_top,SimpleGraph.top_adj]
    intro he
    have hh:=f.injective he
    have hh':j.val=j.val+1:=congrArg Fin.val hh
    omega
  obtain ⟨p,hp,hlen,hsupport⟩:=finite_sequence_simple_walk (SimpleGraph.completeGraph V) n f hadj
  have hdir:∀k,k<p.length→R (p.getVert k) (p.getVert (k+1)):=by
    intro k hk
    have hk':k<n:=by simpa [hlen] using hk
    have hv:∀j:Fin (n+1),p.getVert j.val=f j:=by
      intro j
      have hh:some (p.getVert j.val)=p.support[j.val]? :=p.getVert_eq_support_getElem? (by omega)
      rw [hsupport] at hh
      simpa only [List.getElem?_ofFn,dif_pos (show j.val<n+1 by omega),Option.some.injEq] using hh
    rw [hv ⟨k,by omega⟩,hv ⟨k+1,by omega⟩]
    have hh:=hR (cycleNext ⟨k,by omega⟩)
    have hnex:=hnext ⟨k,hk'⟩
    change cycleNext (cycleNext (⟨k,by omega⟩:Fin (n+1)))=cycleNext (⟨k+1,by omega⟩:Fin (n+1)) at hnex
    rw [hnex] at hh
    exact hh
  have hmem:p.support.toFinset=Finset.univ.image W.1.val:=by
    rw [hsupport]
    ext x
    simp only [List.mem_toFinset,List.mem_ofFn,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨cycleNext i,hi⟩
    · rintro ⟨i,hi⟩
      have hsurj:Function.Surjective (@cycleNext (n+1)):=Finite.injective_iff_surjective.mp cycleNext_injective
      obtain ⟨j,hj⟩:=hsurj i
      exact ⟨j,by simpa [f,hj] using hi⟩
  have hclose:R finish start:=hR 0
  rw [←hf0,←hfn]
  refine ⟨p,hp,hlen,?_,?_,hdir⟩
  · ext x
    have hh:=congrArg (fun s:Finset V=>x∈s) hmem
    exact Iff.of_eq (by simpa only [List.mem_toFinset,Finset.mem_image,Finset.mem_univ,true_and] using hh)
  · simpa only [hf0,hfn] using hclose
end Oberwolfach
