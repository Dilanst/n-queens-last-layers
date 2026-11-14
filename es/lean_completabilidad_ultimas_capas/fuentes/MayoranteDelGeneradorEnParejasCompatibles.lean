import DeLasParejasAlSoporteDelError
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular RealFinita Corte Repair
noncomputable section
open Classical

theorem mayorante_en_parejas {n} {X : State n} {w} (A : Region masas X w (·⁻¹)) (o v j l : Bool) :
    let s:=pesoDeUnaFuente n o*pesoDeUnaFuente n v
    ∑ u∈paresCompatibles n,(s:ℝ)*costoLocal X u.1 u.2 o v j l
      (fun e => (errorDelAtomo A e:ℝ)) (fun w b => (errorDeLinea A w b:ℝ))
      ≤ (costoDeUnPatron A o v j l:ℝ) := by
  intro s
  let total:=fun (g : Mark n→ℝ) => ∑ u∈paresCompatibles n,(s:ℝ)*g u
  let agg (a b j' l' : Bool) (g : Mark n→ℝ≥0) := s*masas.sum (soporteDeParejas X a b j' l') g
  have line (a b j' l' : Bool) (g : Mark n→ℝ≥0) :
      total (fun u => filtrarTasa (patronInverso X u.1 u.2 a b j' l') (g u:ℝ))≤(agg a b j' l' g:ℝ) :=
    cota_de_soporte_ponderada X a b j' l' g s
  let re:=fun w b => (errorDeLinea A w b:ℝ)
  let be:=fun e => (errorDelAtomo A e:ℝ)
  let U:=fun u : Mark n => patronInverso X u.1 u.2 o v j l
  have zero : total (fun _ => 0)=0 := by simp [total]
  have plus (f g : Mark n→ℝ) : total (fun u => f u+g u)=total f+total g := by
    simp [total,mul_add,Finset.sum_add_distrib]
  have sources (first : Bool) :
      total (fun u => sumaFuentes (U u) (if first then o else v) (if first then u.1 else u.2) re)≤
      (↑(∑ i : Fin 4,if (if first then o else v) then 0 else agg o v j l
        (fun u => errorDeLinea A (lineLabel (if first then u.1 else u.2) i) true)):ℝ) := by
    rw [NNReal.coe_sum]
    change (∑ u∈paresCompatibles n,(s:ℝ)* ∑ i : Fin 4,_)≤_
    simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    apply Finset.sum_le_sum; intro i _
    cases hh : (if first then o else v)
    · simpa [U,filtrarTasa,hh,re,total] using
        (line o v j l (fun u => errorDeLinea A (lineLabel (if first then u.1 else u.2) i) true))
    · simp [hh,filtrarTasa]
  have birth₁ :
      total (fun u => filtrarTasa (o=true ∧ patronInverso X u.1 u.2 false v j l) (be u.1))≤
        (↑(if o then agg false v j l (fun u => errorDelAtomo A u.1) else 0):ℝ) := by
    cases o
    · simpa [filtrarTasa] using zero.le
    · simpa [filtrarTasa,be] using line false v j l (fun u => errorDelAtomo A u.1)
  have birth₂ :
      total (fun u => filtrarTasa (v=true ∧ patronInverso X u.1 u.2 o false j l) (be u.2))≤
        (↑(if v then agg o false j l (fun u => errorDelAtomo A u.2) else 0):ℝ) := by
    cases v
    · simpa [filtrarTasa] using zero.le
    · simpa [filtrarTasa,be] using line o false j l (fun u => errorDelAtomo A u.2)
  have dest₂:=line o v true l (fun u => errorDeLinea A (lineLabel (corners u).2 2) j)
  have dest₃:=line o v j true (fun u => errorDeLinea A (lineLabel (corners u).2 3) l)
  have st₁:=sources true
  have st₂:=sources false
  simp only [if_true,Bool.false_eq_true,if_false] at st₁ st₂
  change total (fun u => costoLocal X u.1 u.2 o v j l be re)≤_
  unfold costoLocal inserciones sumaMetas costoDeUnPatron
  simp only [plus,NNReal.coe_add]
  linarith only [birth₁,birth₂,dest₂,dest₃,st₁,st₂]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.mayorante_en_parejas
