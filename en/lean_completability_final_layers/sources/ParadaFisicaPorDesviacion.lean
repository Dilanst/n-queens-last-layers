import RelojDelPrefijoRegular
import RelojEnLosHijosConMasa
import PasosPositivosDeUnaHistoria
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section

def pararPorError {n} (p : FactoresContinuos) (h : ℕ) (um : ℝ≥0) (t : ℕ) (X : State n) :=
  decide (um≤errorDelEstado p h X (fraccionAntes n t))

theorem hasta_el_primer_cruce {n h : ℕ} {p : FactoresContinuos} {κ m ζ C um : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (bal : BalanceMalla n h p C) (hu : um/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ)
    (halt : ℕ→State n→Bool) (sigue : ∀ j X,errorDelEstado p h X (fraccionAntes n j)<um → halt j X=false)
    (T : ℕ) (floor : ζ≤fraccionAntes n T) (i : ℝ≥0×List (ℕ×State n))
    (mem : i∈rutas (pasoParado (coloresDelPerfil n h p) halt) 0 T (0,initial n h)) (nz : i.1≠0)
    (s : ℕ) (sT : s≤T) (antes : ∀ t<s,errorDelEstado p h (estadoEn (0,initial n h) i.2 t).2 (fraccionAntes n t)<um) :
    i.2.length=T ∧ ∀ t≤s, let y:=estadoEn (0,initial n h) i.2 t
      y.1=t ∧ y.2.failed=false ∧ y.2.reals+y.2.virtuals=(2*n-1)-t := by
  obtain ⟨len,steps⟩:=pasos_con_peso mem nz
  refine ⟨len,?_⟩
  intro t ts
  induction t with
  | zero =>
    change 0=0 ∧ false=false ∧ (n-h)+((2*n-1)-(n-h))=(2*n-1)-0
    exact ⟨rfl,rfl,by omega⟩
  | succ t ih =>
    let y:=estadoEn (0,initial n h) i.2 t
    obtain ⟨time,ok,clock⟩:=ih (by omega)
    change y.1=t at time
    change y.2.reals+y.2.virtuals=(2*n-1)-t at clock
    have lt:=antes t (by omega)
    let E:=errorDelEstado p h y.2 (fraccionAntes n t)
    have reg:=el_maximo_da_seguimiento p h y.2 _ (reloj_de_las_cuotas hn clock)
    have he : E/n≤piso κ ζ := (div_le_div_of_nonneg_right lt.le (zero_le _)).trans hu
    let A:=region_del_estado hn hh sp kp m1 zp (fraccion_antes_del_horizonte (by omega : t≤T) floor)
      (fraccion_a_lo_sumo_uno hn t) bal he ho y.2 reg
    obtain ⟨a,am,ap,child⟩:=steps t (by omega)
    have go : halt y.1 y.2=false := by rw [time]; exact sigue t y.2 lt
    change a∈pasoParado _ _ (0+t) y at am
    unfold pasoParado stopped at am; rw [if_neg (by simp [go])] at am
    obtain ⟨b,bm,ab⟩:=List.mem_map.mp am
    subst a
    have good:=hijo_regular_con_masa A y.1 ok b bm ap
    dsimp only at child
    rw [←child]; refine ⟨congrArg (·+1) time,good.1,?_⟩
    change b.2.reals+b.2.virtuals=(2*n-1)-(t+1)
    have eq:=good.2.trans clock; omega
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.hasta_el_primer_cruce
