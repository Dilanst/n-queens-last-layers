import PasoDetenidoDelObservableInverso
import ColaDeUnObservableRealDetenido
import ValorDelTensorEnElHorizonte
import BlancoDiscretoDelConteoInverso
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Trayectoria.Adjunto

theorem cola_inversa_en_un_horizonte {n h T} {p : FactoresContinuos} {κ m ζ C E : ℝ≥0} {L W : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (finT : T≤2*n-1) (floor : ζ≤fraccionAntes n T) (bal : BalanceMalla n h p C)
    (he : E/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ) (w : Cell n→ℝ) (wp : 0≤W) (cap : ∀ z,|w z|≤W)
    (θ a : ℝ) (tp : 0≤θ) (small : θ*(2*(176*constanteRelojInverso κ m ζ W*n))≤1) :
    let S:=pasoDeRaiz (n:=n) h T p E
    let x:ℕ×State n:=(0,initial n h)
    let J:=176*constanteRelojInverso κ m ζ W*n
    let U:=cotaDerivaInversa κ m ζ C E W
    let target:=blancoInverso h p w (horizonteInverso n T 0)
    (avg masas (rutas S 0 T x) (mark masas (fun l =>
      let last:=l.foldl (fun _ y => y) x
      last.1=T ∧ a+T*U≤|inversasDelTablero last.2.physical w-target|))).val ≤
      2*Real.exp ((T:ℝ)*(θ*(2*J))^2-θ*a) := by
  intro S x J U target
  let Φ:=fun v : ℕ×State n => valorInversoAlTiempo h T p w v.1 v.2
  have posK : 0≤constanteRelojInverso κ m ζ W := by unfold constanteRelojInverso; positivity
  have ju : 0≤J := by dsimp only [J]; positivity
  have uu : 0≤U := by dsimp only [U,cotaDerivaInversa]; positivity
  let jn:ℝ≥0:=⟨J,ju⟩
  let un:ℝ≥0:=⟨U,uu⟩
  have pair (t : ℕ) (v : ℕ×State n) := paso_detenido_inverso hn hh sp kp m1 zp finT floor bal he ho w wp cap t v
  have bound:=cola_del_observable_real S Φ un jn (parada_normalizada _ _)
    (fun t v => (pair t v).1) (fun t v => (pair t v).2) T x θ a tp small
  apply le_trans _ bound
  apply NNReal.coe_le_coe.mpr
  apply misma_masa_en_el_soporte
  intro i _ _ massive
  let last:=i.2.foldl (fun _ y => y) x
  obtain ⟨reached,large⟩:=massive
  have start : Φ x=target := blanco_inverso_al_inicio hn h T p w
  have finish : Φ last=inversasDelTablero last.2.physical w := by
    change valorInversoAlTiempo h T p w last.1 last.2=_
    change last.1=T at reached
    rw [reached]; exact horizonte_es_conteo_fisico h T p w last.2
  change a+T*U≤|Φ last-Φ x|
  rwa [start,finish]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cola_inversa_en_un_horizonte
