import CaminoFisicoDelConteoInverso
import VariacionDelBlancoInverso
import ConcentracionFisicaEnElUltimoReloj
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Trayectoria.Adjunto
theorem control_del_inverso_en_el_ultimo_reloj {n h T} {p : FactoresContinuos} {κ m C : ℝ≥0} {L W : ℝ}
    (hn : 2≤n) (tN : T≤2*n-1) (sp : ControlEspacial p κ m L) (kp : 0<κ) (bal : BalanceMalla n h p C)
    (margin : 2*(C:ℝ)≤κ*n) (w : Cell n→ℝ) (wp : 0≤W) (cap : ∀ e,|w e|≤W) (γ : ℝ) :
    let N:=2*n-1
    let S:=kernel masas (coloresDelPerfil n h p) (·⁻¹)
    let X:=fun l j => estadoEn (initial n h) l j
    let y:=horizonteInverso n T 0
    avg masas (rutas S 0 N (initial n h)) (mark masas (fun l =>
      γ*(n:ℝ)^2+4*(n:ℝ)*(↑(N-T):ℝ)*W+2*(1-(y:ℝ))*W*(n:ℝ)^2 ≤
      |inversasDelTablero (X l N).physical w-blancoInverso h p w 1|)) ≤
    avg masas (rutas S 0 T (initial n h)) (mark masas (fun l =>
      γ*(n:ℝ)^2≤|inversasDelTablero (X l T).physical w-blancoInverso h p w y|)) := by
  intro N S X y
  let good:=fun l => γ*(n:ℝ)^2≤|inversasDelTablero (X l T).physical w-blancoInverso h p w y|
  have norm : ∀ t x,total masas (S t x)=1 := kernel_total masas _ _ (fun _ z => inv_mul_cancel₀ z) (by
    intro i j ij
    change masas.add (ns masas i) (ns masas j)≠masas.zero
    rw [ns_real,ns_real]; change (i:ℝ≥0)+j≠0; rw [←Nat.cast_add]; exact_mod_cast ij)
  rw [←probabilidad_del_prefijo S norm (mark masas good) (initial n h) 0 T N tN]
  have hy : y≤1 := by
    dsimp [y,horizonteInverso]
    exact (div_le_one (by exact_mod_cast (by omega : 0<2*n-1))).mpr (by exact_mod_cast tN)
  have target:=variacion_del_blanco_inverso hn sp kp bal margin w wp cap y hy
  apply misma_masa_en_el_soporte
  intro i mem nz bad
  obtain ⟨leg,last,r,le,path⟩:=camino_real_de_una_historia (coloresDelPerfil n h p) i mem nz T N tN le_rfl
  have var:=corte_con_signo path w W wp cap
  rw [←inversas_sin_condicion_de_nivel _ w leg,←inversas_sin_condicion_de_nivel _ w last,abs_sub_comm] at var
  have dur : 4*(n:ℝ)*r*W≤4*(n:ℝ)*(↑(N-T):ℝ)*W := by gcongr
  change |inversasDelTablero (X i.2 N).physical w-inversasDelTablero (X i.2 T).physical w|≤_ at var
  have first:=abs_sub_le (inversasDelTablero (X i.2 N).physical w) (inversasDelTablero (X i.2 T).physical w)
    (blancoInverso h p w 1)
  have second:=abs_sub_le (inversasDelTablero (X i.2 T).physical w) (blancoInverso h p w y) (blancoInverso h p w 1)
  have take : X (i.2.take T) T=X i.2 T := by simp only [X,estadoEn,List.take_take,min_self]
  change γ*(n:ℝ)^2≤|inversasDelTablero (X (i.2.take T) T).physical w-blancoInverso h p w y|
  rw [take]
  change γ*(n:ℝ)^2+4*(n:ℝ)*(↑(N-T):ℝ)*W+2*(1-(y:ℝ))*W*(n:ℝ)^2≤_ at bad
  linarith only [first,second,bad,var,dur,target]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.control_del_inverso_en_el_ultimo_reloj
