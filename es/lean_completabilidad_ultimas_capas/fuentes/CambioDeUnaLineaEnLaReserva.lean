import MasaEsperadaDeLasCandidatasReservadas
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical
open scoped BigOperators
/-- Masa de una condición puntual bajo la densidad de entrada. -/
def pesoCuando (p : Prop) (w : ℝ) : ℝ:=if p then w else 0

def masaBajo {n} (w : Cell n→ℝ) (P : Cell n→Prop) : ℝ :=
  ∑ e : Cell n,pesoCuando (P e) (w e)

theorem masaBajo_mono {n} (w : Cell n→ℝ) (pos : ∀ e,0≤w e) {P Q : Cell n→Prop}
    (sub : ∀ e,P e→Q e) : masaBajo w P≤masaBajo w Q := by
  apply Finset.sum_le_sum
  intro e _
  by_cases h : P e
  · simp [pesoCuando,h,sub e h]
  · by_cases g : Q e <;> simp [pesoCuando,h,g,pos]

theorem acuerdo_igual_fuera_de_las_etiquetas {ι : Type} [DecidableEq ι] (R N : Finset ι)
    (ω ω' : ι→Bool) (j : ι) (off : ∀ i,i≠j→ω i=ω' i) (r : j∉R) (s : j∉N) :
    acuerdoDeReserva R N ω↔acuerdoDeReserva R N ω' := by
  have eqR (i) (hi : i∈R) : ω i=ω' i:=off i (fun e=>r (e ▸ hi))
  have eqN (i) (hi : i∈N) : ω i=ω' i:=off i (fun e=>s (e ▸ hi))
  constructor <;> intro h
  · exact ⟨fun i hi=>(eqR i hi).symm.trans (h.1 i hi),fun i hi=>(eqN i hi).symm.trans (h.2 i hi)⟩
  · exact ⟨fun i hi=>(eqR i hi).trans (h.1 i hi),fun i hi=>(eqN i hi).trans (h.2 i hi)⟩

theorem cambio_marcado_por_tres_fibras {n} (w : Cell n→ℝ) (pos : ∀ e,0≤w e) (z : Cell n)
    (ω ω' : LineaReservable n→Bool) (j : LineaReservable n) (off : ∀ i,i≠j→ω i=ω' i) :
    |masaMarcadaB1 w z ω-masaMarcadaB1 w z ω'|≤
      masaBajo w (fun e=>j∈lineasPropias (corners (z,e)).1)+
      masaBajo w (fun e=>j∈lineasPropias (corners (z,e)).2)+masaBajo w (fun e=>j∈lineasPropias e) := by
  let P (e : Cell n):=lineasPropias (corners (z,e)).1
  let Q (e : Cell n):=lineasPropias (corners (z,e)).2
  let N (e : Cell n):=lineasPropias e
  let val (ω : LineaReservable n→Bool) e : ℝ:=if acuerdoDeReserva (P e∪Q e) (N e) ω then w e else 0
  have single (e : Cell n) : |val ω e-val ω' e|≤w e:=by
    unfold val
    split <;> split <;> simp [abs_of_nonneg (pos e),pos]
  have all (e : Cell n) : |val ω e-val ω' e|≤
      pesoCuando (j∈P e) (w e)+pesoCuando (j∈Q e) (w e)+pesoCuando (j∈N e) (w e):=by
    by_cases r : j∈P e <;> by_cases s : j∈Q e <;> by_cases u : j∈N e
    all_goals try {simp only [pesoCuando,r,s,u,if_true,if_false]; linarith only [single e,pos e]}
    have eq:=acuerdo_igual_fuera_de_las_etiquetas (P e∪Q e) (N e) ω ω' j off (by simpa using And.intro r s) u
    by_cases h : acuerdoDeReserva (P e∪Q e) (N e) ω
    · simp [val,pesoCuando,r,s,u,h,eq.mp h]
    · have neg : ¬acuerdoDeReserva (P e∪Q e) (N e) ω':=fun h'=>h (eq.mpr h')
      simp [val,pesoCuando,r,s,u,h,neg]
  change |(∑ e,val ω e)-(∑ e,val ω' e)|≤_
  rw [←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simpa only [Finset.sum_add_distrib,masaBajo,P,Q,N] using
    (Finset.sum_le_sum (s:=Finset.univ) (fun e _=>all e))

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.masaBajo_mono
#print axioms ArticuloA.Historias.acuerdo_igual_fuera_de_las_etiquetas
#print axioms ArticuloA.Historias.cambio_marcado_por_tres_fibras
