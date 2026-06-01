import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block309

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block309

open Set

def block309W1 : Rat := ((2433214463935793 : Rat) / 2500000000000000)
def block309W2 : Rat := ((1412448135664609 : Rat) / 25000000000000000)
def block309W3 : Rat := ((5256841923431329 : Rat) / 20000000000000000)
def block309W4 : Rat := (0 : Rat)
def block309S1 : Rat := ((18174751 : Rat) / 10000000)
def block309S2 : Rat := ((511587 : Rat) / 200000)
def block309S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block309S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block309V (y : ℝ) : ℝ :=
  ratPotential block309W1 block309W2 block309W3 block309W4 block309S1 block309S2 block309S3 block309S4 y

def block309LeftParamsCertificate : Bool :=
  allBoxesSameParams block309LeftBoxes block309W1 block309W2 block309W3 block309W4 block309S1 block309S2 block309S3 block309S4

theorem block309LeftParamsCertificate_eq_true :
    block309LeftParamsCertificate = true := by
  native_decide

theorem block309_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block309LeftL : ℝ) (block309LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block309S1 : ℝ))
    (hy2ne : y ≠ (block309S2 : ℝ))
    (hy3ne : y ≠ (block309S3 : ℝ))
    (hy4ne : y ≠ (block309S4 : ℝ)) :
    0 < block309V y := by
  have hcert := block309LeftCertificate_eq_true
  unfold block309LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block309LeftBoxes) (lo := block309LeftL) (hi := block309LeftR)
    (w1 := block309W1) (w2 := block309W2) (w3 := block309W3) (w4 := block309W4)
    (s1 := block309S1) (s2 := block309S2) (s3 := block309S3) (s4 := block309S4)
    hboxes hcover block309LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block309RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block309RightChunk000 block309W1 block309W2 block309W3 block309W4 block309S1 block309S2 block309S3 block309S4

theorem block309RightChunk000ParamsCertificate_eq_true :
    block309RightChunk000ParamsCertificate = true := by
  native_decide

theorem block309_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block309RightChunk000L : ℝ) (block309RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block309S1 : ℝ))
    (hy2ne : y ≠ (block309S2 : ℝ))
    (hy3ne : y ≠ (block309S3 : ℝ))
    (hy4ne : y ≠ (block309S4 : ℝ)) :
    0 < block309V y := by
  have hcert := block309RightChunk000Certificate_eq_true
  unfold block309RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block309RightChunk000) (lo := block309RightChunk000L) (hi := block309RightChunk000R)
    (w1 := block309W1) (w2 := block309W2) (w3 := block309W3) (w4 := block309W4)
    (s1 := block309S1) (s2 := block309S2) (s3 := block309S3) (s4 := block309S4)
    hboxes hcover block309RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block309_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block309RightL : ℝ) (block309RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block309S1 : ℝ))
    (hy2ne : y ≠ (block309S2 : ℝ))
    (hy3ne : y ≠ (block309S3 : ℝ))
    (hy4ne : y ≠ (block309S4 : ℝ)) :
    0 < block309V y := by
  have hL : (block309RightChunk000L : ℝ) = (block309RightL : ℝ) := by
    norm_num [block309RightChunk000L, block309RightL]
  have hR : (block309RightChunk000R : ℝ) = (block309RightR : ℝ) := by
    norm_num [block309RightChunk000R, block309RightR]
  have hyc : y ∈ Icc (block309RightChunk000L : ℝ) (block309RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block309_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block309_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block309LeftL : ℝ) (block309LeftR : ℝ) →
    y ≠ 0 → y ≠ (block309S1 : ℝ) → y ≠ (block309S2 : ℝ) →
    y ≠ (block309S3 : ℝ) → y ≠ (block309S4 : ℝ) → 0 < block309V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block309RightL : ℝ) (block309RightR : ℝ) →
    y ≠ 0 → y ≠ (block309S1 : ℝ) → y ≠ (block309S2 : ℝ) →
    y ≠ (block309S3 : ℝ) → y ≠ (block309S4 : ℝ) → 0 < block309V y)

theorem block309_reallog_certificate_proof :
    block309_reallog_certificate := by
  exact ⟨block309_left_V_pos, block309_right_V_pos⟩

end Block309
end M1817475
end Erdos1038Lean
