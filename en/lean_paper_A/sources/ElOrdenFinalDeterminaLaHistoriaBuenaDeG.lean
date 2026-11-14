import SoporteDeLasHistoriasDelProcesoGuiado
import Mathlib.Data.List.Permutation
namespace ArticuloA.Historias
open Perfil Trayectoria Trayectoria.E2 Trayectoria.ProfileKernel RealFinita Repair
open scoped BigOperators NNReal
noncomputable section
open Classical

def reconstruirDesdeLaListaFinal {n} (v : List (Cell n)) : ℕ→List (EstadoGuiado n)
  | 0 => []
  | j+1 => some (v.drop j)::reconstruirDesdeLaListaFinal v j

theorem un_orden_final_reconstruye_la_historia {n} (ρ : Cell n→ℝ≥0) (q : ℕ)
    (U : Cell n→Cell n→Prop) (d : ℝ≥0) (t : ℕ) (l : List (Cell n)) (hist : List (EstadoGuiado n))
    (path : transicionesDeCamino (pasoDeG ρ q) t (some l) hist)
    (ok : prefijoRegular (condicionDeSeguimientoG ρ q U d) t (some l) hist)
    {v : List (Cell n)} (ends : ultimoEstado (some l) hist=some v) :
    v.drop hist.length=l ∧ reconstruirDesdeLaListaFinal v hist.length=hist := by
  induction hist generalizing t l with
  | nil =>
    change some l=some v at ends
    simp [Option.some.inj ends,reconstruirDesdeLaListaFinal]
  | cons y tail ih =>
    obtain ⟨⟨w,hy⟩,rest⟩:=path
    obtain ⟨reg,remainder⟩:=ok
    obtain ⟨e,rfl,_,_⟩:=origen_regular_agrega_casilla ρ q t l reg.1.ne' w y hy
    obtain ⟨prior,states⟩:=ih (t+1) (e::l) rest remainder ends
    constructor
    · change v.drop (tail.length+1)=l
      rw [←List.drop_drop,prior]
      rfl
    · simp [reconstruirDesdeLaListaFinal,prior,states]

/-- A set of q squares represents at most q! regular histories of G. -/
theorem multiplicidad_de_historias_regulares_de_G {n q : ℕ} (ρ : Cell n→ℝ≥0)
    (U : Cell n→Cell n→Prop) (d : ℝ≥0) (g : Finset (List (EstadoGuiado n)))
    (O : Finset (Finset (Cell n))) (size : ∀ S∈O,S.card=q)
    (good : ∀ l∈g,transicionesDeCamino (pasoDeG ρ q) 0 (some []) l ∧ l.length=q ∧
      prefijoRegular (condicionDeSeguimientoG ρ q U d) 0 (some []) l ∧
      ∃ v,ultimoEstado (some []) l=some v ∧ v.toFinset∈O) :
    g.card≤q.factorial*O.card := by
  let enc (S : Finset (Cell n)):=S.toList.permutations.toFinset.image (fun v=>reconstruirDesdeLaListaFinal v q)
  have sub : g⊆O.biUnion enc := by
    intro l hl
    obtain ⟨path,sz,ok,v,finish,mem⟩:=good l hl
    obtain ⟨v',last,law,_,_,_⟩:=terminal_regular_de_G ρ q U d 0 [] l .nil (by simp) path ok
    rw [finish] at last
    cases Option.some.inj last
    have nod : v.Nodup:=law.imp (fun comp eq=>comp.1 (congrArg Prod.fst eq))
    have order:=List.perm_of_nodup_nodup_toFinset_eq nod (Finset.nodup_toList v.toFinset)
      (by simp : v.toFinset=v.toFinset.toList.toFinset)
    have code:=(un_orden_final_reconstruye_la_historia ρ q U d 0 [] l path ok finish).2
    rw [sz] at code
    apply Finset.mem_biUnion.mpr ⟨_,mem,?_⟩
    exact Finset.mem_image.mpr ⟨v,List.mem_toFinset.mpr (List.mem_permutations.mpr order),code⟩
  have cap (S : Finset (Cell n)) (hs : S∈O) : (enc S).card≤q.factorial := by
    calc
      _ ≤ S.toList.permutations.toFinset.card := Finset.card_image_le
      _ ≤ S.toList.permutations.length := List.toFinset_card_le _
      _ = _ := by rw [List.length_permutations,Finset.length_toList,size S hs]
  calc
    g.card ≤ (O.biUnion enc).card := Finset.card_le_card sub
    _ ≤ ∑ S∈O,(enc S).card := Finset.card_biUnion_le
    _ ≤ ∑ _S∈O,q.factorial := Finset.sum_le_sum cap
    _ = _ := by simp [Nat.mul_comm]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.multiplicidad_de_historias_regulares_de_G
