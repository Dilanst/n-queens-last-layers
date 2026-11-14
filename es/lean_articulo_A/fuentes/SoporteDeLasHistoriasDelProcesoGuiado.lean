import TransicionesDelProcesoGuiadoConReserva
import ColaDeVisitasEnHistoriasRegulares
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

open Classical
variable {X : Type}

def transicionesDeCamino (P : ℕ→X→Atoms ℝ≥0 X) (t : ℕ) (x : X) : List X→Prop
  | []=>True
  | y::l=>(∃ w,(w,y)∈P t x) ∧ transicionesDeCamino P (t+1) y l

theorem rutas_siguen_su_ley (P : ℕ→X→Atoms ℝ≥0 X) (t m : ℕ) (x : X) (a : ℝ≥0×List X)
    (ha : a∈rutas P t m x) : transicionesDeCamino P t x a.2 ∧ a.2.length=m := by
  induction m generalizing t x a with
  | zero=>
    simp only [rutas,point,List.mem_singleton] at ha
    subst a
    exact ⟨trivial,rfl⟩
  | succ m ih=>
    change a∈List.flatMap _ (P t x) at ha
    obtain ⟨u,hu,ha⟩:=List.mem_flatMap.mp ha
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha
    obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hi
    obtain ⟨path,len⟩:=ih (t+1) u.2 v hv
    exact ⟨⟨⟨u.1,hu⟩,path⟩,by simp [len]⟩

theorem origen_regular_agrega_casilla {n} (ρ : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n))
    (W : total masas (opcionesGuiadas ρ q t l)≠0) (w : ℝ≥0) (y : EstadoGuiado n)
    (hy : (w,y)∈pasoDeG ρ q t (some l)) :
    ∃ e,y=some (e::l) ∧ ρ e≠0 ∧ ∀ c∈l,compatible e c := by
  let row:=opcionesGuiadas ρ q t l
  let put (e : Cell n) : EstadoGuiado n:=some (e::l)
  have M : total masas (row.map (fun i=>(i.1,put i.2)))=total masas row:=avg_push masas row put _
  change (w,y)∈ProfileKernel.choose masas (row.map (fun i=>(i.1,put i.2))) none (·⁻¹) at hy
  unfold ProfileKernel.choose at hy
  split at hy
  · rename_i h
    exact False.elim (W (M.symm.trans h))
  obtain ⟨v,hv,eq⟩:=List.mem_map.mp hy
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hv
  change i∈List.map _ (List.filter _ (board n)) at hi
  obtain ⟨e,he,rfl⟩:=List.mem_map.mp hi
  exact ⟨e,(congrArg Prod.snd eq).symm,of_decide_eq_true (List.mem_filter.mp he).2⟩

def ultimoEstado (x : X) : List X→X
  | []=>x
  | y::l=>ultimoEstado y l

theorem terminal_regular_de_G {n} (ρ : Cell n→ℝ≥0) (q : ℕ) (U : Cell n→Cell n→Prop) (d : ℝ≥0)
    (t : ℕ) (l : List (Cell n)) (hist : List (EstadoGuiado n))
    (legal : l.Pairwise compatible) (soporte : ∀ e∈l,ρ e≠0)
    (path : transicionesDeCamino (pasoDeG ρ q) t (some l) hist)
    (ok : prefijoRegular (condicionDeSeguimientoG ρ q U d) t (some l) hist) :
    ∃ v,ultimoEstado (some l) hist=some v ∧ v.Pairwise compatible ∧ (∀ e∈v,ρ e≠0) ∧
      v.length=l.length+hist.length ∧ ∀ S : Cell n→Prop,
      (v.toFinset.filter S).card=(l.toFinset.filter S).card+
        visitasDeCamino (fun _ _ y=>observaCabeza S y) t (some l) hist := by
  induction hist generalizing t l with
  | nil=>exact ⟨l,rfl,legal,soporte,by simp,fun _=>by simp [visitasDeCamino]⟩
  | cons y tail ih=>
    obtain ⟨⟨w,hy⟩,rest⟩:=path
    obtain ⟨reg,reg'⟩:=ok
    obtain ⟨e,rfl,pos,compat⟩:=origen_regular_agrega_casilla ρ q t l reg.1.ne' w y hy
    have nod : e∉l:=fun h=>(compat e h).1 rfl
    have supported : ∀ v∈e::l,ρ v≠0:=by
      intro v hv
      rcases List.mem_cons.mp hv with rfl|hm
      · exact pos
      · exact soporte v hm
    obtain ⟨v,ev,pw,sup,len,counts⟩:=ih (t+1) (e::l) (List.pairwise_cons.mpr ⟨compat,legal⟩) supported rest reg'
    refine ⟨v,ev,pw,sup,by simp at len ⊢; omega,?_⟩
    intro S
    have c:=counts S
    by_cases h : S e <;> simp [visitasDeCamino,observaCabeza,h,Finset.filter_insert,nod] at c ⊢ <;> omega

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.rutas_siguen_su_ley
#print axioms ArticuloA.Historias.origen_regular_agrega_casilla
#print axioms ArticuloA.Historias.terminal_regular_de_G
