import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block487

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block487

open Set

def block487W1 : Rat := ((4957448577441907 : Rat) / 10000000000000000)
def block487W2 : Rat := (0 : Rat)
def block487W3 : Rat := ((39047553381657507 : Rat) / 100000000000000000)
def block487W4 : Rat := ((3476746436942903 : Rat) / 100000000000000000)
def block487S1 : Rat := ((18174751 : Rat) / 10000000)
def block487S2 : Rat := ((511587 : Rat) / 200000)
def block487S3 : Rat := ((130613142053571428709 : Rat) / 50000000000000000000)
def block487S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block487V (y : ℝ) : ℝ :=
  ratPotential block487W1 block487W2 block487W3 block487W4 block487S1 block487S2 block487S3 block487S4 y

def block487LeftParamsCertificate : Bool :=
  allBoxesSameParams block487LeftBoxes block487W1 block487W2 block487W3 block487W4 block487S1 block487S2 block487S3 block487S4

theorem block487LeftParamsCertificate_eq_true :
    block487LeftParamsCertificate = true := by
  native_decide

theorem block487_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block487LeftL : ℝ) (block487LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block487S1 : ℝ))
    (hy2ne : y ≠ (block487S2 : ℝ))
    (hy3ne : y ≠ (block487S3 : ℝ))
    (hy4ne : y ≠ (block487S4 : ℝ)) :
    0 < block487V y := by
  have hcert := block487LeftCertificate_eq_true
  unfold block487LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block487LeftBoxes) (lo := block487LeftL) (hi := block487LeftR)
    (w1 := block487W1) (w2 := block487W2) (w3 := block487W3) (w4 := block487W4)
    (s1 := block487S1) (s2 := block487S2) (s3 := block487S3) (s4 := block487S4)
    hboxes hcover block487LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block487RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block487RightChunk000 block487W1 block487W2 block487W3 block487W4 block487S1 block487S2 block487S3 block487S4

theorem block487RightChunk000ParamsCertificate_eq_true :
    block487RightChunk000ParamsCertificate = true := by
  native_decide

theorem block487_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block487RightChunk000L : ℝ) (block487RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block487S1 : ℝ))
    (hy2ne : y ≠ (block487S2 : ℝ))
    (hy3ne : y ≠ (block487S3 : ℝ))
    (hy4ne : y ≠ (block487S4 : ℝ)) :
    0 < block487V y := by
  have hcert := block487RightChunk000Certificate_eq_true
  unfold block487RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block487RightChunk000) (lo := block487RightChunk000L) (hi := block487RightChunk000R)
    (w1 := block487W1) (w2 := block487W2) (w3 := block487W3) (w4 := block487W4)
    (s1 := block487S1) (s2 := block487S2) (s3 := block487S3) (s4 := block487S4)
    hboxes hcover block487RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block487_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block487RightL : ℝ) (block487RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block487S1 : ℝ))
    (hy2ne : y ≠ (block487S2 : ℝ))
    (hy3ne : y ≠ (block487S3 : ℝ))
    (hy4ne : y ≠ (block487S4 : ℝ)) :
    0 < block487V y := by
  have hL : (block487RightChunk000L : ℝ) = (block487RightL : ℝ) := by
    norm_num [block487RightChunk000L, block487RightL]
  have hR : (block487RightChunk000R : ℝ) = (block487RightR : ℝ) := by
    norm_num [block487RightChunk000R, block487RightR]
  have hyc : y ∈ Icc (block487RightChunk000L : ℝ) (block487RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block487_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block487_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block487LeftL : ℝ) (block487LeftR : ℝ) →
    y ≠ 0 → y ≠ (block487S1 : ℝ) → y ≠ (block487S2 : ℝ) →
    y ≠ (block487S3 : ℝ) → y ≠ (block487S4 : ℝ) → 0 < block487V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block487RightL : ℝ) (block487RightR : ℝ) →
    y ≠ 0 → y ≠ (block487S1 : ℝ) → y ≠ (block487S2 : ℝ) →
    y ≠ (block487S3 : ℝ) → y ≠ (block487S4 : ℝ) → 0 < block487V y)

theorem block487_reallog_certificate_proof :
    block487_reallog_certificate := by
  exact ⟨block487_left_V_pos, block487_right_V_pos⟩

end Block487
end M1817475
end Erdos1038Lean
