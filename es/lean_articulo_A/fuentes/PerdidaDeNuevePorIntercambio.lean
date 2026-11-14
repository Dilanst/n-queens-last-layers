import ConjuntosDeCasillasDelTableroFisico
import PerdidaPaso
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical

theorem legal_de_un_subconjunto {n} {p u : Placement n} (hp : Legal p)
    (h : ∀ e∈queens u,e∈queens p) : Legal u := by
  apply (legal_iff_pares_del_soporte u).mpr
  intro a ha b hb ne
  exact legal_pair hp (h _ (by simpa [soporteFisico] using ha))
    (h _ (by simpa [soporteFisico] using hb)) ne

theorem quitar_una_reina_conserva_legalidad {n} {p : Placement n} {c : Cell n}
    (hp : Legal p) (hc : c∈queens p) : Legal (toggle c p) := by
  apply legal_de_un_subconjunto hp
  intro e he
  by_cases h : e=c
  · exact h ▸ hc
  · simpa [mem_toggle,h] using he

theorem intercambio_pierde_a_lo_sumo_nueve {n q : ℕ} {p : Placement n} {m : Mark n}
    (ok : Direct q p m) (z : Cell n) :
    physicalCount p z ≤ physicalCount (forward m p) z + 9 := by
  let a:=(corners m).1
  let b:=(corners m).2
  let p₁:=toggle m.2 p
  let p₂:=toggle a p₁
  let p₃:=forward m p
  have hp₁ : Legal p₁:=quitar_una_reina_conserva_legalidad ok.2.1 ok.2.2.2.1
  have inv:=forward_valid ok
  have hp₂ : Legal p₂:=by
    have hi:=quitar_una_reina_conserva_legalidad inv.2.1 inv.2.2.2.2.1
    simpa [p₂,p₁,p₃,a,b,forward] using hi
  have old : m.2∉queens p₁:=by simp [p₁,mem_toggle,ok.2.2.2.1]
  have a_empty : a∉queens p₁:=by
    have ab : a≠b:=inv.2.2.1
    have ha : a∈queens p₂:=by
      simpa [a,b,p₂,p₁,forward,mem_toggle,ab] using inv.2.2.2.1
    simpa [p₂,mem_toggle] using ha
  have b_empty : b∉queens p₂:=by
    have hb : b∈queens (toggle b p₂):=inv.2.2.2.2.1
    simpa [mem_toggle] using hb
  have h₁ : physicalCount p z≤physicalCount p₁ z+1:=by
    simpa [p₁] using (step_counts p₁ z m.2 hp₁ old).2
  have h₂:= (step_counts p₁ z a hp₁ a_empty).1
  have h₃:= (step_counts p₂ z b hp₂ b_empty).1
  change physicalCount p₁ z≤physicalCount p₂ z+4 at h₂
  change physicalCount p₂ z≤physicalCount (forward m p) z+4 at h₃
  omega

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.legal_de_un_subconjunto
#print axioms ArticuloA.Historias.quitar_una_reina_conserva_legalidad
#print axioms ArticuloA.Historias.intercambio_pierde_a_lo_sumo_nueve
