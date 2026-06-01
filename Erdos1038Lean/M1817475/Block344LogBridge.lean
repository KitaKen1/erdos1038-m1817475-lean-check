import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block344

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block344

open Set

def block344W1 : Rat := ((9189273727476001 : Rat) / 10000000000000000)
def block344W2 : Rat := ((4745623717054629 : Rat) / 100000000000000000)
def block344W3 : Rat := ((7366056140907719 : Rat) / 50000000000000000)
def block344W4 : Rat := ((13778216259028853 : Rat) / 100000000000000000)
def block344S1 : Rat := ((18174751 : Rat) / 10000000)
def block344S2 : Rat := ((511587 : Rat) / 200000)
def block344S3 : Rat := ((26681732875000000003 : Rat) / 10000000000000000000)
def block344S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block344V (y : ℝ) : ℝ :=
  ratPotential block344W1 block344W2 block344W3 block344W4 block344S1 block344S2 block344S3 block344S4 y

def block344LeftParamsCertificate : Bool :=
  allBoxesSameParams block344LeftBoxes block344W1 block344W2 block344W3 block344W4 block344S1 block344S2 block344S3 block344S4

theorem block344LeftParamsCertificate_eq_true :
    block344LeftParamsCertificate = true := by
  native_decide

theorem block344_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block344LeftL : ℝ) (block344LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block344S1 : ℝ))
    (hy2ne : y ≠ (block344S2 : ℝ))
    (hy3ne : y ≠ (block344S3 : ℝ))
    (hy4ne : y ≠ (block344S4 : ℝ)) :
    0 < block344V y := by
  have hcert := block344LeftCertificate_eq_true
  unfold block344LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block344LeftBoxes) (lo := block344LeftL) (hi := block344LeftR)
    (w1 := block344W1) (w2 := block344W2) (w3 := block344W3) (w4 := block344W4)
    (s1 := block344S1) (s2 := block344S2) (s3 := block344S3) (s4 := block344S4)
    hboxes hcover block344LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block344RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block344RightChunk000 block344W1 block344W2 block344W3 block344W4 block344S1 block344S2 block344S3 block344S4

theorem block344RightChunk000ParamsCertificate_eq_true :
    block344RightChunk000ParamsCertificate = true := by
  native_decide

theorem block344_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block344RightChunk000L : ℝ) (block344RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block344S1 : ℝ))
    (hy2ne : y ≠ (block344S2 : ℝ))
    (hy3ne : y ≠ (block344S3 : ℝ))
    (hy4ne : y ≠ (block344S4 : ℝ)) :
    0 < block344V y := by
  have hcert := block344RightChunk000Certificate_eq_true
  unfold block344RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block344RightChunk000) (lo := block344RightChunk000L) (hi := block344RightChunk000R)
    (w1 := block344W1) (w2 := block344W2) (w3 := block344W3) (w4 := block344W4)
    (s1 := block344S1) (s2 := block344S2) (s3 := block344S3) (s4 := block344S4)
    hboxes hcover block344RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block344_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block344RightL : ℝ) (block344RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block344S1 : ℝ))
    (hy2ne : y ≠ (block344S2 : ℝ))
    (hy3ne : y ≠ (block344S3 : ℝ))
    (hy4ne : y ≠ (block344S4 : ℝ)) :
    0 < block344V y := by
  have hL : (block344RightChunk000L : ℝ) = (block344RightL : ℝ) := by
    norm_num [block344RightChunk000L, block344RightL]
  have hR : (block344RightChunk000R : ℝ) = (block344RightR : ℝ) := by
    norm_num [block344RightChunk000R, block344RightR]
  have hyc : y ∈ Icc (block344RightChunk000L : ℝ) (block344RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block344_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block344_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block344LeftL : ℝ) (block344LeftR : ℝ) →
    y ≠ 0 → y ≠ (block344S1 : ℝ) → y ≠ (block344S2 : ℝ) →
    y ≠ (block344S3 : ℝ) → y ≠ (block344S4 : ℝ) → 0 < block344V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block344RightL : ℝ) (block344RightR : ℝ) →
    y ≠ 0 → y ≠ (block344S1 : ℝ) → y ≠ (block344S2 : ℝ) →
    y ≠ (block344S3 : ℝ) → y ≠ (block344S4 : ℝ) → 0 < block344V y)

theorem block344_reallog_certificate_proof :
    block344_reallog_certificate := by
  exact ⟨block344_left_V_pos, block344_right_V_pos⟩

end Block344
end M1817475
end Erdos1038Lean
