import ConcentracionInversaAntesDelCorte
import DelProcesoDetenidoALaLeyOriginal
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Trayectoria.Adjunto
theorem concentracion_inversa_en_la_ley_original {n h T} {p : FactoresContinuos} {κ m ζ C E : ℝ≥0} {L W : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (finT : T≤2*n-1) (floor : ζ≤fraccionAntes n T) (bal : BalanceMalla n h p C)
    (he : E/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ) (w : Cell n→ℝ) (wp : 0≤W) (cap : ∀ z,|w z|≤W)
    (ε s : ℝ) (ep : 0<ε) (st : 0<s)
    (sm : s*(2*(176*constanteRelojInverso κ m ζ W))≤1)
    (tilt : 32*(176*constanteRelojInverso κ m ζ W)^2*s≤ε)
    (size : cotaDerivaInversa κ m ζ C E W≤ε*n/4) :
    let ley:=rutas (kernel masas (coloresDelPerfil n h p) (·⁻¹)) 0 T (initial n h)
    let target:=blancoInverso h p w (horizonteInverso n T 0)
    (avg masas ley (mark masas (fun l => ε*(n:ℝ)^2≤
      |inversasDelTablero (estadoEn (initial n h) l T).physical w-target|))).val ≤
      (avg masas ley (mark masas (salidaOriginal p h T E))).val + 2*Real.exp (-(s*ε/4)*(n:ℝ)) := by
  intro ley target
  let B:=fun X : State n => ε*(n:ℝ)^2≤|inversasDelTablero X.physical w-target|
  have cmp:=evento_al_corte_en_la_ley_original hn hh sp kp m1 zp floor bal he ho B
  exact cmp.trans (add_le_add_left (cola_exponencial_del_conteo_inverso
    hn hh sp kp m1 zp finT floor bal he ho w wp cap ε s ep st sm tilt size) _)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.concentracion_inversa_en_la_ley_original
