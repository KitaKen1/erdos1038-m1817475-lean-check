import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block496

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block496

open Set

def block496W1 : Rat := ((4721906009373597 : Rat) / 10000000000000000)
def block496W2 : Rat := (0 : Rat)
def block496W3 : Rat := ((8142201061901817 : Rat) / 20000000000000000)
def block496W4 : Rat := ((2471739262302013 : Rat) / 100000000000000000)
def block496S1 : Rat := ((18174751 : Rat) / 10000000)
def block496S2 : Rat := ((511587 : Rat) / 200000)
def block496S3 : Rat := ((130437200089285714431 : Rat) / 50000000000000000000)
def block496S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block496V (y : ℝ) : ℝ :=
  ratPotential block496W1 block496W2 block496W3 block496W4 block496S1 block496S2 block496S3 block496S4 y

def block496LeftParamsCertificate : Bool :=
  allBoxesSameParams block496LeftBoxes block496W1 block496W2 block496W3 block496W4 block496S1 block496S2 block496S3 block496S4

theorem block496LeftParamsCertificate_eq_true :
    block496LeftParamsCertificate = true := by
  native_decide

theorem block496_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block496LeftL : ℝ) (block496LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block496S1 : ℝ))
    (hy2ne : y ≠ (block496S2 : ℝ))
    (hy3ne : y ≠ (block496S3 : ℝ))
    (hy4ne : y ≠ (block496S4 : ℝ)) :
    0 < block496V y := by
  have hcert := block496LeftCertificate_eq_true
  unfold block496LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block496LeftBoxes) (lo := block496LeftL) (hi := block496LeftR)
    (w1 := block496W1) (w2 := block496W2) (w3 := block496W3) (w4 := block496W4)
    (s1 := block496S1) (s2 := block496S2) (s3 := block496S3) (s4 := block496S4)
    hboxes hcover block496LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block496RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block496RightChunk000 block496W1 block496W2 block496W3 block496W4 block496S1 block496S2 block496S3 block496S4

theorem block496RightChunk000ParamsCertificate_eq_true :
    block496RightChunk000ParamsCertificate = true := by
  native_decide

theorem block496_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block496RightChunk000L : ℝ) (block496RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block496S1 : ℝ))
    (hy2ne : y ≠ (block496S2 : ℝ))
    (hy3ne : y ≠ (block496S3 : ℝ))
    (hy4ne : y ≠ (block496S4 : ℝ)) :
    0 < block496V y := by
  have hcert := block496RightChunk000Certificate_eq_true
  unfold block496RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block496RightChunk000) (lo := block496RightChunk000L) (hi := block496RightChunk000R)
    (w1 := block496W1) (w2 := block496W2) (w3 := block496W3) (w4 := block496W4)
    (s1 := block496S1) (s2 := block496S2) (s3 := block496S3) (s4 := block496S4)
    hboxes hcover block496RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block496_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block496RightL : ℝ) (block496RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block496S1 : ℝ))
    (hy2ne : y ≠ (block496S2 : ℝ))
    (hy3ne : y ≠ (block496S3 : ℝ))
    (hy4ne : y ≠ (block496S4 : ℝ)) :
    0 < block496V y := by
  have hL : (block496RightChunk000L : ℝ) = (block496RightL : ℝ) := by
    norm_num [block496RightChunk000L, block496RightL]
  have hR : (block496RightChunk000R : ℝ) = (block496RightR : ℝ) := by
    norm_num [block496RightChunk000R, block496RightR]
  have hyc : y ∈ Icc (block496RightChunk000L : ℝ) (block496RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block496_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block496_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block496LeftL : ℝ) (block496LeftR : ℝ) →
    y ≠ 0 → y ≠ (block496S1 : ℝ) → y ≠ (block496S2 : ℝ) →
    y ≠ (block496S3 : ℝ) → y ≠ (block496S4 : ℝ) → 0 < block496V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block496RightL : ℝ) (block496RightR : ℝ) →
    y ≠ 0 → y ≠ (block496S1 : ℝ) → y ≠ (block496S2 : ℝ) →
    y ≠ (block496S3 : ℝ) → y ≠ (block496S4 : ℝ) → 0 < block496V y)

theorem block496_reallog_certificate_proof :
    block496_reallog_certificate := by
  exact ⟨block496_left_V_pos, block496_right_V_pos⟩

end Block496
end M1817475
end Erdos1038Lean
