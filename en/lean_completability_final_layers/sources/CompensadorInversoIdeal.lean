import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
namespace ArticuloA.Inversa

/-- Each of the four positions is a linear form in two marks. The two
queen positions use (O,χ), and the two diagonal positions use (V,χ). -/
def pairForm (O χ θ : ℝ) := O+θ*χ

def tensor (O₁ χ₁ O₂ χ₂ V₁ ξ₁ V₂ ξ₂ θ₁ θ₂ x₁ x₂ : ℝ) :=
  pairForm O₁ χ₁ θ₁ * pairForm O₂ χ₂ θ₂ * pairForm V₁ ξ₁ (-x₁) * pairForm V₂ ξ₂ (-x₂)

/-- Generator on the separated (ideal) four-factor basis by linearity on
the 16 monomials. The true random transition need not obey a product rule. -/
def productRule (u v w z du dv dw dz : ℝ) :=
  du*v*w*z + u*dv*w*z + u*v*dw*z + u*v*w*dz

theorem separar_derivadas (u v w z a b c d a' b' c' d' : ℝ)
    (h₁ : a+a'=0) (h₂ : b+b'=0) (h₃ : c+c'=0) (h₄ : d+d'=0) :
    productRule u v w z a b c d + productRule u v w z a' b' c' d' = 0 := by
  have H : productRule u v w z a b c d + productRule u v w z a' b' c' d' =
      productRule u v w z (a+a') (b+b') (c+c') (d+d') := by unfold productRule; ring
  rw [H,h₁,h₂,h₃,h₄]; simp [productRule]

/-- Exact scalar coefficient equations for Δy' = z' = -1/N. The slope
formulas are given explicitly; this lemma is an algebraic identity. -/
theorem factores (N z y π p : ℝ) (hn : N ≠ 0) (hz : z ≠ 0) :
    let α := 1/(N*z)
    let θ := π*y/z^4
    let ξ := p*y/z
    let θ' := -π/(N*z^4) + 4*π*y/(N*z^5)
    let ξ' := -p/(N*z) + p*y/(N*z^2)
    θ' + π/(N*z^4) - 4*α*θ = 0 ∧ ξ' + p/(N*z) - α*ξ = 0 := by
  dsimp
  constructor <;> field_simp [hn,hz] <;> ring

theorem adjunto_del_par (O₁ χ₁ O₂ χ₂ V₁ ξ₁ V₂ ξ₂ θ₁ θ₂ x₁ x₂
    a k₁ k₂ b₁ b₂ d₁ d₂ s₁ s₂ : ℝ)
    (h₁ : d₁+k₁-4*a*θ₁=0) (h₂ : d₂+k₂-4*a*θ₂=0)
    (h₃ : s₁+b₁-a*x₁=0) (h₄ : s₂+b₂-a*x₂=0) :
    let u := pairForm O₁ χ₁ θ₁
    let v := pairForm O₂ χ₂ θ₂
    let w := pairForm V₁ ξ₁ (-x₁)
    let z := pairForm V₂ ξ₂ (-x₂)
    productRule u v w z (d₁*χ₁) (d₂*χ₂) (-s₁*ξ₁) (-s₂*ξ₂) +
      productRule u v w z ((k₁-4*a*θ₁)*χ₁) ((k₂-4*a*θ₂)*χ₂)
        ((-b₁+a*x₁)*ξ₁) ((-b₂+a*x₂)*ξ₂) = 0 := by
  intro u v w z
  apply separar_derivadas <;> first
    | linear_combination χ₁*h₁
    | linear_combination χ₂*h₂
    | linear_combination -ξ₁*h₃
    | linear_combination -ξ₂*h₄

theorem terminal (O₁ χ₁ O₂ χ₂ V₁ ξ₁ V₂ ξ₂ : ℝ) :
    tensor O₁ χ₁ O₂ χ₂ V₁ ξ₁ V₂ ξ₂ 0 0 0 0 = O₁*O₂*V₁*V₂ := by simp [tensor,pairForm]

theorem inicial (y π₁ π₂ p₁ p₂ : ℝ) :
    tensor 0 1 0 1 1 1 1 1 (π₁*y) (π₂*y) (p₁*y) (p₂*y) =
      y^2*π₁*π₂*(1-y*p₁)*(1-y*p₂) := by unfold tensor pairForm; ring
end ArticuloA.Inversa
#print axioms ArticuloA.Inversa.factores
#print axioms ArticuloA.Inversa.adjunto_del_par
#print axioms ArticuloA.Inversa.inicial
