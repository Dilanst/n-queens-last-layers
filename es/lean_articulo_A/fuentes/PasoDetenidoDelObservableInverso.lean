import DerivaDelObservableInversoEnE2
import ParadaDeLasReparacionesDirectas
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Trayectoria.Adjunto

theorem paso_detenido_inverso {n h T} {p : FactoresContinuos} {κ m ζ C E : ℝ≥0} {L W : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (finT : T≤2*n-1) (floor : ζ≤fraccionAntes n T) (bal : BalanceMalla n h p C)
    (he : E/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ) (w : Cell n→ℝ) (wp : 0≤W) (cap : ∀ z,|w z|≤W)
    (t : ℕ) (x : ℕ×State n) :
    let S:=pasoDeRaiz h T p E
    let Φ:=fun v : ℕ×State n => valorInversoAlTiempo h T p w v.1 v.2
    let K:=constanteRelojInverso κ m ζ W
    (∀ i∈S t x,|Φ i.2-Φ x|≤176*K*n) ∧
      |media (S t x) (fun y => Φ y-Φ x)|≤cotaDerivaInversa κ m ζ C E W := by
  intro S Φ K
  rcases x with ⟨j,X⟩
  have kp' : 0≤K := by dsimp only [K,constanteRelojInverso]; positivity
  by_cases stop : freezeAt T (pararRaiz h p E) j X=true
  · change (∀ i∈(stopped masas _ _ t (j,X)),_) ∧ |media (stopped masas _ _ t (j,X)) _|≤_
    simp only [stopped,stop,if_true,point,List.mem_singleton]
    constructor
    · intro i hi; subst i; simp only [sub_self,abs_zero]; positivity
    · simp only [media,sub_self,mul_zero,add_zero,abs_zero]
      dsimp only [cotaDerivaInversa,constanteRelojInverso]; positivity
  · have go:=(Bool.or_eq_false_iff.mp (Bool.eq_false_of_not_eq_true stop))
    have jt : j<T := by simpa [decide_eq_false_iff_not] using go.1
    have ok : coherent X ∧ X.failed=false ∧ Seguimiento h p X (fraccionAntes n j) E := by
      simpa [pararRaiz] using go.2
    have hz:=fraccion_antes_del_horizonte jt.le floor
    let A:=region_del_estado hn hh sp kp m1 zp hz (fraccion_a_lo_sumo_uno hn j) bal he ho X ok.2.2
    have rem : X.reals+X.virtuals≠0 := by
      intro zero; apply A.running
      change ns masas X.reals+ns masas X.virtuals=0
      rw [ns_real,ns_real,←Nat.cast_add,zero,Nat.cast_zero]
    let col:=coloresDelPerfil n h p
    let row:=choices masas X col (·⁻¹)
    have kernelEq:=kernel_is_row masas X j col (·⁻¹) ok.2.1 rem
    change (∀ i∈(stopped masas (kernel masas col (·⁻¹)) _ t (j,X)),_) ∧
      |media (stopped masas (kernel masas col (·⁻¹)) _ t (j,X)) _|≤_
    simp only [stopped,stop,Bool.false_eq_true,if_false,kernelEq]
    constructor
    · intro i hi
      obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hi
      obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hv
      exact (salto_y_resto_en_el_reloj hn sp kp w wp cap zp jt finT floor X a.2 ok.1
        (row_allowed masas X col (·⁻¹) a ha)).1
    · rw [media_map _ (fun Y : State n => (j+1,Y)) _,media_map _ (next X) _]
      exact deriva_del_observable_inverso hn hh sp kp m1 zp jt finT floor bal he ho X ok.2.2 ok.1 ok.2.1 w wp cap

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.paso_detenido_inverso
