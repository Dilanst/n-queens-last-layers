import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
namespace ArticuloA.Perfil
noncomputable section
variable {𝕜 : Type} [Field 𝕜]

/-- L is the same integration functional for the inner pair (i,j) in Γ and a.
Only extraction of an external scalar is used, which also holds for quadrature. -/
theorem factor_inverso {R C : Type*}
    (L : ((R × C) → 𝕜) → 𝕜) (hom : ∀ c f, L (fun x => c*f x) = c*L f)
    (b : 𝕜) (rR : R → 𝕜) (rC : C → 𝕜) (ψ ν : R → C → 𝕜)
    (perfil : ∀ i j, ν i j = b*rR i*rC j*ψ i j) (r : R) (c : C) :
    L (fun x => ν r x.2 * ν x.1 c * ψ x.1 x.2) =
    b*rR r*rC c * L (fun x => ν x.1 x.2 * ψ r x.2 * ψ x.1 c) := by
  rw [←hom]; congr 1; funext x
  simp only [perfil]; ring

/-- Product integration outside the pointwise identity, for w=1/a.
The positive lower bound on a in §9 implies the nonvanishing used here. -/
theorem masa_inversa {R C : Type*} (lr : (R → 𝕜) → 𝕜) (lc : (C → 𝕜) → 𝕜)
    (hr : ∀ z f, lr (fun x => z*f x) = z*lr f)
    (hc : ∀ z f, lc (fun x => z*f x) = z*lc f)
    (b : 𝕜) (rR : R → 𝕜) (rC : C → 𝕜) (Γ a : R → C → 𝕜)
    (massR : lr rR = 1) (massC : lc rC = 1)
    (nz : ∀ r c, a r c ≠ 0)
    (factor : ∀ r c, Γ r c = b*rR r*rC c*a r c) :
    lr (fun r => lc (fun c => Γ r c / a r c)) = b := by
  have eq (r : R) (c : C) : Γ r c / a r c = (b*rR r)*rC c := by
    rw [factor]; exact mul_div_cancel_right₀ _ (nz _ _)
  simp_rw [eq,hc,massC,mul_one]
  rw [hr,massR,mul_one]
end
end ArticuloA.Perfil
#print axioms ArticuloA.Perfil.factor_inverso
#print axioms ArticuloA.Perfil.masa_inversa
