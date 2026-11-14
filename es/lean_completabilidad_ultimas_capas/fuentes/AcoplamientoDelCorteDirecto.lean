import AcuerdoDeLeyesEnLosPrefijos
import ConcentracionDeCandidatosEnElCorte
import RegularidadDeE2HastaElCorte
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.Adjunto Trayectoria.ProfileKernel RealFinita Corte
noncomputable section
open Classical

def abiertosDeRaiz {n} (h T : ℕ) (p : FactoresContinuos) (u : ℝ≥0) (_ : ℕ) (y : ℕ×State n) :=
  !(freezeAt T (pararRaiz h p u) y.1 y.2)

theorem sigue_la_raiz_hasta_T {n h T : ℕ} {p : FactoresContinuos} {κ m ζ C u : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (bal : BalanceMalla n h p C) (hu : u/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ)
    (floor : ζ≤fraccionAntes n T) (i : ℝ≥0×List (ℕ×State n))
    (mem : i∈rutas (pasoParado (coloresDelPerfil n h p) (fun _ _ => false)) 0 T (0,initial n h)) (nz : i.1≠0)
    (regular : ¬salidaOriginal p h T u (i.2.map Prod.snd)) :
    prefijoAbierto (abiertosDeRaiz h T p u) 0 (0,initial n h) i.2 ∧
    (i.2.foldl (fun _ y => y) (0,initial n h)).1=T := by
  let x:ℕ×State n:=(0,initial n h)
  let Y:=fun j => estadoEn x i.2 j
  have small (j : ℕ) (jt : j≤T) : errorDelEstado p h (Y j).2 (fraccionAntes n j)<u := by
    apply lt_of_not_ge; intro large
    exact regular ⟨j,jt,Or.inr (by rw [←estado_al_olvidar_el_reloj 0 (initial n h) i.2 j]; exact large)⟩
  have path:=hasta_el_primer_cruce hn hh sp kp m1 zp bal hu ho (fun _ _ => false) (fun _ _ _ => rfl)
    T floor i mem nz T le_rfl (fun j jt => small j jt.le)
  have coh:=coherencia_en_el_prefijo (coloresDelPerfil n h p) (fun _ _ => false) x (initial_coherent n h) 0 T i mem nz
  refine ⟨prefijo_desde_indices _ 0 x i.2 ?_,?_⟩
  · intro j jl
    have jt : j<T := by rwa [path.1] at jl
    obtain ⟨clock,live,quota⟩:=path.2 j jt.le
    change (Y j).1=j at clock
    have tr:=el_maximo_da_seguimiento p h (Y j).2 _ (reloj_de_las_cuotas hn quota)
    have cap : errorDelEstado p h (Y j).2 (fraccionAntes n j)/n≤u/n :=
      div_le_div_of_nonneg_right (small j jt.le).le (zero_le _)
    have reg : Seguimiento h p (Y j).2 (fraccionAntes n j) u :=
      ⟨tr.reloj,grow masas tr.piezas cap,fun line al => grow masas (tr.grados line al) cap,
        grow masas tr.masa cap,fun f => grow masas (tr.virtual f) cap⟩
    have pass : pararRaiz h p u j (Y j).2=false := by simp [pararRaiz,coh j jt.le,live,reg,Y,x]
    change (!(freezeAt T (pararRaiz h p u) (Y j).1 (Y j).2))=true
    rw [clock]; simp [freezeAt,not_le.mpr jt,pass]
  · have t:=(path.2 T le_rfl).1
    unfold estadoEn at t
    rwa [List.take_of_length_le (le_of_eq path.1)] at t

theorem coincide_la_ley_de_la_raiz {n h T : ℕ} (p : FactoresContinuos) (u : ℝ≥0)
    (g : List (ℕ×State n)→ℝ≥0) :
    let x:ℕ×State n:=(0,initial n h)
    let ok:=abiertosDeRaiz (n:=n) h T p u
    avg masas (rutas (pasoParado (coloresDelPerfil n h p) (fun _ _ => false)) 0 T x)
      (fun l => if prefijoAbierto ok 0 x l then g l else 0)=
    avg masas (rutas (pasoDeRaiz h T p u) 0 T x) (fun l => if prefijoAbierto ok 0 x l then g l else 0) := by
  intro x ok
  apply ley_en_los_prefijos_abiertos
  intro j y open'
  have live : freezeAt T (pararRaiz h p u) y.1 y.2=false := by simpa only [ok,abiertosDeRaiz,Bool.not_eq_true'] using open'
  simp only [pasoParado,pasoDeRaiz,stopped,live,Bool.false_eq_true,if_false]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.sigue_la_raiz_hasta_T
#print axioms ArticuloA.Historias.coincide_la_ley_de_la_raiz
