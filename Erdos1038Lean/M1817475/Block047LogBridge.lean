import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block047

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block047

open Set

def block047W1 : Rat := ((2627203050231391 : Rat) / 1000000000000000)
def block047W2 : Rat := (0 : Rat)
def block047W3 : Rat := (0 : Rat)
def block047W4 : Rat := ((541629645199433 : Rat) / 2000000000000000)
def block047S1 : Rat := ((18174751 : Rat) / 10000000)
def block047S2 : Rat := ((511587 : Rat) / 200000)
def block047S3 : Rat := ((107000619 : Rat) / 40000000)
def block047S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block047V (y : ℝ) : ℝ :=
  ratPotential block047W1 block047W2 block047W3 block047W4 block047S1 block047S2 block047S3 block047S4 y

def block047LeftParamsCertificate : Bool :=
  allBoxesSameParams block047LeftBoxes block047W1 block047W2 block047W3 block047W4 block047S1 block047S2 block047S3 block047S4

theorem block047LeftParamsCertificate_eq_true :
    block047LeftParamsCertificate = true := by
  native_decide

theorem block047_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block047LeftL : ℝ) (block047LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block047S1 : ℝ))
    (hy2ne : y ≠ (block047S2 : ℝ))
    (hy3ne : y ≠ (block047S3 : ℝ))
    (hy4ne : y ≠ (block047S4 : ℝ)) :
    0 < block047V y := by
  have hcert := block047LeftCertificate_eq_true
  unfold block047LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block047LeftBoxes) (lo := block047LeftL) (hi := block047LeftR)
    (w1 := block047W1) (w2 := block047W2) (w3 := block047W3) (w4 := block047W4)
    (s1 := block047S1) (s2 := block047S2) (s3 := block047S3) (s4 := block047S4)
    hboxes hcover block047LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block047RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block047RightChunk000 block047W1 block047W2 block047W3 block047W4 block047S1 block047S2 block047S3 block047S4

theorem block047RightChunk000ParamsCertificate_eq_true :
    block047RightChunk000ParamsCertificate = true := by
  native_decide

theorem block047_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block047RightChunk000L : ℝ) (block047RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block047S1 : ℝ))
    (hy2ne : y ≠ (block047S2 : ℝ))
    (hy3ne : y ≠ (block047S3 : ℝ))
    (hy4ne : y ≠ (block047S4 : ℝ)) :
    0 < block047V y := by
  have hcert := block047RightChunk000Certificate_eq_true
  unfold block047RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block047RightChunk000) (lo := block047RightChunk000L) (hi := block047RightChunk000R)
    (w1 := block047W1) (w2 := block047W2) (w3 := block047W3) (w4 := block047W4)
    (s1 := block047S1) (s2 := block047S2) (s3 := block047S3) (s4 := block047S4)
    hboxes hcover block047RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block047_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block047RightL : ℝ) (block047RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block047S1 : ℝ))
    (hy2ne : y ≠ (block047S2 : ℝ))
    (hy3ne : y ≠ (block047S3 : ℝ))
    (hy4ne : y ≠ (block047S4 : ℝ)) :
    0 < block047V y := by
  have hL : (block047RightChunk000L : ℝ) = (block047RightL : ℝ) := by
    norm_num [block047RightChunk000L, block047RightL]
  have hR : (block047RightChunk000R : ℝ) = (block047RightR : ℝ) := by
    norm_num [block047RightChunk000R, block047RightR]
  have hyc : y ∈ Icc (block047RightChunk000L : ℝ) (block047RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block047_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block047_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block047LeftL : ℝ) (block047LeftR : ℝ) →
    y ≠ 0 → y ≠ (block047S1 : ℝ) → y ≠ (block047S2 : ℝ) →
    y ≠ (block047S3 : ℝ) → y ≠ (block047S4 : ℝ) → 0 < block047V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block047RightL : ℝ) (block047RightR : ℝ) →
    y ≠ 0 → y ≠ (block047S1 : ℝ) → y ≠ (block047S2 : ℝ) →
    y ≠ (block047S3 : ℝ) → y ≠ (block047S4 : ℝ) → 0 < block047V y)

theorem block047_reallog_certificate_proof :
    block047_reallog_certificate := by
  exact ⟨block047_left_V_pos, block047_right_V_pos⟩

end Block047
end M1817475
end Erdos1038Lean
