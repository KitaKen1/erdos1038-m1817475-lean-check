import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block498

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block498

open Set

def block498W1 : Rat := ((11670130259741969 : Rat) / 25000000000000000)
def block498W2 : Rat := (0 : Rat)
def block498W3 : Rat := ((4112084976190743 : Rat) / 10000000000000000)
def block498W4 : Rat := ((2216804975264239 : Rat) / 100000000000000000)
def block498S1 : Rat := ((18174751 : Rat) / 10000000)
def block498S2 : Rat := ((511587 : Rat) / 200000)
def block498S3 : Rat := ((130398101875000000147 : Rat) / 50000000000000000000)
def block498S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block498V (y : ℝ) : ℝ :=
  ratPotential block498W1 block498W2 block498W3 block498W4 block498S1 block498S2 block498S3 block498S4 y

def block498LeftParamsCertificate : Bool :=
  allBoxesSameParams block498LeftBoxes block498W1 block498W2 block498W3 block498W4 block498S1 block498S2 block498S3 block498S4

theorem block498LeftParamsCertificate_eq_true :
    block498LeftParamsCertificate = true := by
  native_decide

theorem block498_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block498LeftL : ℝ) (block498LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block498S1 : ℝ))
    (hy2ne : y ≠ (block498S2 : ℝ))
    (hy3ne : y ≠ (block498S3 : ℝ))
    (hy4ne : y ≠ (block498S4 : ℝ)) :
    0 < block498V y := by
  have hcert := block498LeftCertificate_eq_true
  unfold block498LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block498LeftBoxes) (lo := block498LeftL) (hi := block498LeftR)
    (w1 := block498W1) (w2 := block498W2) (w3 := block498W3) (w4 := block498W4)
    (s1 := block498S1) (s2 := block498S2) (s3 := block498S3) (s4 := block498S4)
    hboxes hcover block498LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block498RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block498RightChunk000 block498W1 block498W2 block498W3 block498W4 block498S1 block498S2 block498S3 block498S4

theorem block498RightChunk000ParamsCertificate_eq_true :
    block498RightChunk000ParamsCertificate = true := by
  native_decide

theorem block498_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block498RightChunk000L : ℝ) (block498RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block498S1 : ℝ))
    (hy2ne : y ≠ (block498S2 : ℝ))
    (hy3ne : y ≠ (block498S3 : ℝ))
    (hy4ne : y ≠ (block498S4 : ℝ)) :
    0 < block498V y := by
  have hcert := block498RightChunk000Certificate_eq_true
  unfold block498RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block498RightChunk000) (lo := block498RightChunk000L) (hi := block498RightChunk000R)
    (w1 := block498W1) (w2 := block498W2) (w3 := block498W3) (w4 := block498W4)
    (s1 := block498S1) (s2 := block498S2) (s3 := block498S3) (s4 := block498S4)
    hboxes hcover block498RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block498_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block498RightL : ℝ) (block498RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block498S1 : ℝ))
    (hy2ne : y ≠ (block498S2 : ℝ))
    (hy3ne : y ≠ (block498S3 : ℝ))
    (hy4ne : y ≠ (block498S4 : ℝ)) :
    0 < block498V y := by
  have hL : (block498RightChunk000L : ℝ) = (block498RightL : ℝ) := by
    norm_num [block498RightChunk000L, block498RightL]
  have hR : (block498RightChunk000R : ℝ) = (block498RightR : ℝ) := by
    norm_num [block498RightChunk000R, block498RightR]
  have hyc : y ∈ Icc (block498RightChunk000L : ℝ) (block498RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block498_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block498_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block498LeftL : ℝ) (block498LeftR : ℝ) →
    y ≠ 0 → y ≠ (block498S1 : ℝ) → y ≠ (block498S2 : ℝ) →
    y ≠ (block498S3 : ℝ) → y ≠ (block498S4 : ℝ) → 0 < block498V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block498RightL : ℝ) (block498RightR : ℝ) →
    y ≠ 0 → y ≠ (block498S1 : ℝ) → y ≠ (block498S2 : ℝ) →
    y ≠ (block498S3 : ℝ) → y ≠ (block498S4 : ℝ) → 0 < block498V y)

theorem block498_reallog_certificate_proof :
    block498_reallog_certificate := by
  exact ⟨block498_left_V_pos, block498_right_V_pos⟩

end Block498
end M1817475
end Erdos1038Lean
