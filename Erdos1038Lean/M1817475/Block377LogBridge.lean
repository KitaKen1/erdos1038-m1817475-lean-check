import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block377

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block377

open Set

def block377W1 : Rat := ((8551245605469473 : Rat) / 10000000000000000)
def block377W2 : Rat := ((1165530831939389 : Rat) / 25000000000000000)
def block377W3 : Rat := ((7865769051127887 : Rat) / 50000000000000000)
def block377W4 : Rat := ((2802276557638767 : Rat) / 20000000000000000)
def block377S1 : Rat := ((18174751 : Rat) / 10000000)
def block377S2 : Rat := ((511587 : Rat) / 200000)
def block377S3 : Rat := ((132763543839285714329 : Rat) / 50000000000000000000)
def block377S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block377V (y : ℝ) : ℝ :=
  ratPotential block377W1 block377W2 block377W3 block377W4 block377S1 block377S2 block377S3 block377S4 y

def block377LeftParamsCertificate : Bool :=
  allBoxesSameParams block377LeftBoxes block377W1 block377W2 block377W3 block377W4 block377S1 block377S2 block377S3 block377S4

theorem block377LeftParamsCertificate_eq_true :
    block377LeftParamsCertificate = true := by
  native_decide

theorem block377_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block377LeftL : ℝ) (block377LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block377S1 : ℝ))
    (hy2ne : y ≠ (block377S2 : ℝ))
    (hy3ne : y ≠ (block377S3 : ℝ))
    (hy4ne : y ≠ (block377S4 : ℝ)) :
    0 < block377V y := by
  have hcert := block377LeftCertificate_eq_true
  unfold block377LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block377LeftBoxes) (lo := block377LeftL) (hi := block377LeftR)
    (w1 := block377W1) (w2 := block377W2) (w3 := block377W3) (w4 := block377W4)
    (s1 := block377S1) (s2 := block377S2) (s3 := block377S3) (s4 := block377S4)
    hboxes hcover block377LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block377RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block377RightChunk000 block377W1 block377W2 block377W3 block377W4 block377S1 block377S2 block377S3 block377S4

theorem block377RightChunk000ParamsCertificate_eq_true :
    block377RightChunk000ParamsCertificate = true := by
  native_decide

theorem block377_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block377RightChunk000L : ℝ) (block377RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block377S1 : ℝ))
    (hy2ne : y ≠ (block377S2 : ℝ))
    (hy3ne : y ≠ (block377S3 : ℝ))
    (hy4ne : y ≠ (block377S4 : ℝ)) :
    0 < block377V y := by
  have hcert := block377RightChunk000Certificate_eq_true
  unfold block377RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block377RightChunk000) (lo := block377RightChunk000L) (hi := block377RightChunk000R)
    (w1 := block377W1) (w2 := block377W2) (w3 := block377W3) (w4 := block377W4)
    (s1 := block377S1) (s2 := block377S2) (s3 := block377S3) (s4 := block377S4)
    hboxes hcover block377RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block377_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block377RightL : ℝ) (block377RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block377S1 : ℝ))
    (hy2ne : y ≠ (block377S2 : ℝ))
    (hy3ne : y ≠ (block377S3 : ℝ))
    (hy4ne : y ≠ (block377S4 : ℝ)) :
    0 < block377V y := by
  have hL : (block377RightChunk000L : ℝ) = (block377RightL : ℝ) := by
    norm_num [block377RightChunk000L, block377RightL]
  have hR : (block377RightChunk000R : ℝ) = (block377RightR : ℝ) := by
    norm_num [block377RightChunk000R, block377RightR]
  have hyc : y ∈ Icc (block377RightChunk000L : ℝ) (block377RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block377_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block377_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block377LeftL : ℝ) (block377LeftR : ℝ) →
    y ≠ 0 → y ≠ (block377S1 : ℝ) → y ≠ (block377S2 : ℝ) →
    y ≠ (block377S3 : ℝ) → y ≠ (block377S4 : ℝ) → 0 < block377V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block377RightL : ℝ) (block377RightR : ℝ) →
    y ≠ 0 → y ≠ (block377S1 : ℝ) → y ≠ (block377S2 : ℝ) →
    y ≠ (block377S3 : ℝ) → y ≠ (block377S4 : ℝ) → 0 < block377V y)

theorem block377_reallog_certificate_proof :
    block377_reallog_certificate := by
  exact ⟨block377_left_V_pos, block377_right_V_pos⟩

end Block377
end M1817475
end Erdos1038Lean
