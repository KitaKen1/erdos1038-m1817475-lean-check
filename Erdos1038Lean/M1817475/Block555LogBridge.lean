import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block555

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block555

open Set

def block555W1 : Rat := ((3829020084069369 : Rat) / 10000000000000000)
def block555W2 : Rat := (0 : Rat)
def block555W3 : Rat := ((11542910345623851 : Rat) / 25000000000000000)
def block555W4 : Rat := (0 : Rat)
def block555S1 : Rat := ((18174751 : Rat) / 10000000)
def block555S2 : Rat := ((511587 : Rat) / 200000)
def block555S3 : Rat := ((129283802767857143053 : Rat) / 50000000000000000000)
def block555S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block555V (y : ℝ) : ℝ :=
  ratPotential block555W1 block555W2 block555W3 block555W4 block555S1 block555S2 block555S3 block555S4 y

def block555LeftParamsCertificate : Bool :=
  allBoxesSameParams block555LeftBoxes block555W1 block555W2 block555W3 block555W4 block555S1 block555S2 block555S3 block555S4

theorem block555LeftParamsCertificate_eq_true :
    block555LeftParamsCertificate = true := by
  native_decide

theorem block555_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block555LeftL : ℝ) (block555LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block555S1 : ℝ))
    (hy2ne : y ≠ (block555S2 : ℝ))
    (hy3ne : y ≠ (block555S3 : ℝ))
    (hy4ne : y ≠ (block555S4 : ℝ)) :
    0 < block555V y := by
  have hcert := block555LeftCertificate_eq_true
  unfold block555LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block555LeftBoxes) (lo := block555LeftL) (hi := block555LeftR)
    (w1 := block555W1) (w2 := block555W2) (w3 := block555W3) (w4 := block555W4)
    (s1 := block555S1) (s2 := block555S2) (s3 := block555S3) (s4 := block555S4)
    hboxes hcover block555LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block555RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block555RightChunk000 block555W1 block555W2 block555W3 block555W4 block555S1 block555S2 block555S3 block555S4

theorem block555RightChunk000ParamsCertificate_eq_true :
    block555RightChunk000ParamsCertificate = true := by
  native_decide

theorem block555_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block555RightChunk000L : ℝ) (block555RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block555S1 : ℝ))
    (hy2ne : y ≠ (block555S2 : ℝ))
    (hy3ne : y ≠ (block555S3 : ℝ))
    (hy4ne : y ≠ (block555S4 : ℝ)) :
    0 < block555V y := by
  have hcert := block555RightChunk000Certificate_eq_true
  unfold block555RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block555RightChunk000) (lo := block555RightChunk000L) (hi := block555RightChunk000R)
    (w1 := block555W1) (w2 := block555W2) (w3 := block555W3) (w4 := block555W4)
    (s1 := block555S1) (s2 := block555S2) (s3 := block555S3) (s4 := block555S4)
    hboxes hcover block555RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block555_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block555RightL : ℝ) (block555RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block555S1 : ℝ))
    (hy2ne : y ≠ (block555S2 : ℝ))
    (hy3ne : y ≠ (block555S3 : ℝ))
    (hy4ne : y ≠ (block555S4 : ℝ)) :
    0 < block555V y := by
  have hL : (block555RightChunk000L : ℝ) = (block555RightL : ℝ) := by
    norm_num [block555RightChunk000L, block555RightL]
  have hR : (block555RightChunk000R : ℝ) = (block555RightR : ℝ) := by
    norm_num [block555RightChunk000R, block555RightR]
  have hyc : y ∈ Icc (block555RightChunk000L : ℝ) (block555RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block555_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block555_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block555LeftL : ℝ) (block555LeftR : ℝ) →
    y ≠ 0 → y ≠ (block555S1 : ℝ) → y ≠ (block555S2 : ℝ) →
    y ≠ (block555S3 : ℝ) → y ≠ (block555S4 : ℝ) → 0 < block555V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block555RightL : ℝ) (block555RightR : ℝ) →
    y ≠ 0 → y ≠ (block555S1 : ℝ) → y ≠ (block555S2 : ℝ) →
    y ≠ (block555S3 : ℝ) → y ≠ (block555S4 : ℝ) → 0 < block555V y)

theorem block555_reallog_certificate_proof :
    block555_reallog_certificate := by
  exact ⟨block555_left_V_pos, block555_right_V_pos⟩

end Block555
end M1817475
end Erdos1038Lean
