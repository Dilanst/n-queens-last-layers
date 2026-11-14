import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import CandidatosDeLasLineasReservadas
import EsperanzaRealFinita
open scoped BigOperators
namespace ArticuloA.Historias
open Set
noncomputable section
open Classical

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def pesoDeBernoulli (τ : ℝ) (b : Bool) : ℝ := if b then τ else 1-τ
def masaDeReserva (τ : ℝ) (ω : ι→Bool) : ℝ := ∏ i,pesoDeBernoulli τ (ω i)

theorem normalizacion_de_la_reserva (τ : ℝ) : ∑ ω : ι→Bool,masaDeReserva τ ω=1 := by
  unfold masaDeReserva
  rw [←Fintype.prod_sum]
  simp [Fintype.sum_bool,pesoDeBernoulli]

omit [DecidableEq ι] in
theorem masa_de_reserva_no_negativa (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) (ω : ι→Bool) : 0≤masaDeReserva τ ω := by
  apply Finset.prod_nonneg
  intro i _
  cases ω i <;> simp [pesoDeBernoulli,hτ.1,hτ.2]

def acuerdoDeReserva (R N : Finset ι) (ω : ι→Bool) : Prop :=
  (∀ i∈R,ω i=true) ∧ (∀ i∈N,ω i=false)

theorem probabilidad_de_un_patron_de_reserva (τ : ℝ) (R N : Finset ι) (dis : Disjoint R N) :
    ∑ ω : ι→Bool,(if acuerdoDeReserva R N ω then masaDeReserva τ ω else 0)=τ^R.card*(1-τ)^N.card := by
  let gate (i : ι) (b : Bool) : ℝ:=if (i∈R → b=true) ∧ (i∈N → b=false) then 1 else 0
  have factor (ω : ι→Bool) :
      (if acuerdoDeReserva R N ω then masaDeReserva τ ω else 0)=
        ∏ i,(pesoDeBernoulli τ (ω i)*gate i (ω i)):=by
    by_cases h : acuerdoDeReserva R N ω
    · have all (i : ι) : gate i (ω i)=1:=if_pos ⟨h.1 i,h.2 i⟩
      simp [h,all,masaDeReserva]
    · have missing : ∃ i,¬((i∈R → ω i=true) ∧ (i∈N → ω i=false)):=by
        by_contra! all
        exact h ⟨fun i=> (all i).1,fun i=> (all i).2⟩
      obtain ⟨i,hi⟩:=missing
      rw [if_neg h]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [gate,hi]
  have one (i : ι) : (∑ b : Bool,pesoDeBernoulli τ b*gate i b)=
      (if i∈R then τ else 1)*(if i∈N then 1-τ else 1):=by
    by_cases r : i∈R <;> by_cases s : i∈N
    · exact False.elim (Finset.disjoint_left.mp dis r s)
    all_goals simp [Fintype.sum_bool,gate,pesoDeBernoulli,r,s]
  simp_rw [factor]
  rw [←Fintype.prod_sum (fun (i : ι) (b : Bool)=>pesoDeBernoulli τ b*gate i b)]
  simp_rw [one]
  rw [Finset.prod_mul_distrib,Fintype.prod_ite_mem,Fintype.prod_ite_mem]
  simp

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.normalizacion_de_la_reserva
#print axioms ArticuloA.Historias.masa_de_reserva_no_negativa
#print axioms ArticuloA.Historias.probabilidad_de_un_patron_de_reserva
