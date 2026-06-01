import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block052

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block052

open Set

def block052W1 : Rat := ((1356603518190053 : Rat) / 500000000000000)
def block052W2 : Rat := (0 : Rat)
def block052W3 : Rat := (0 : Rat)
def block052W4 : Rat := ((2668856358092361 : Rat) / 10000000000000000)
def block052S1 : Rat := ((18174751 : Rat) / 10000000)
def block052S2 : Rat := ((511587 : Rat) / 200000)
def block052S3 : Rat := ((107000619 : Rat) / 40000000)
def block052S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block052V (y : ℝ) : ℝ :=
  ratPotential block052W1 block052W2 block052W3 block052W4 block052S1 block052S2 block052S3 block052S4 y

def block052LeftParamsCertificate : Bool :=
  allBoxesSameParams block052LeftBoxes block052W1 block052W2 block052W3 block052W4 block052S1 block052S2 block052S3 block052S4

theorem block052LeftParamsCertificate_eq_true :
    block052LeftParamsCertificate = true := by
  native_decide

theorem block052_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block052LeftL : ℝ) (block052LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block052S1 : ℝ))
    (hy2ne : y ≠ (block052S2 : ℝ))
    (hy3ne : y ≠ (block052S3 : ℝ))
    (hy4ne : y ≠ (block052S4 : ℝ)) :
    0 < block052V y := by
  have hcert := block052LeftCertificate_eq_true
  unfold block052LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block052LeftBoxes) (lo := block052LeftL) (hi := block052LeftR)
    (w1 := block052W1) (w2 := block052W2) (w3 := block052W3) (w4 := block052W4)
    (s1 := block052S1) (s2 := block052S2) (s3 := block052S3) (s4 := block052S4)
    hboxes hcover block052LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block052RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block052RightChunk000 block052W1 block052W2 block052W3 block052W4 block052S1 block052S2 block052S3 block052S4

theorem block052RightChunk000ParamsCertificate_eq_true :
    block052RightChunk000ParamsCertificate = true := by
  native_decide

theorem block052_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block052RightChunk000L : ℝ) (block052RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block052S1 : ℝ))
    (hy2ne : y ≠ (block052S2 : ℝ))
    (hy3ne : y ≠ (block052S3 : ℝ))
    (hy4ne : y ≠ (block052S4 : ℝ)) :
    0 < block052V y := by
  have hcert := block052RightChunk000Certificate_eq_true
  unfold block052RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block052RightChunk000) (lo := block052RightChunk000L) (hi := block052RightChunk000R)
    (w1 := block052W1) (w2 := block052W2) (w3 := block052W3) (w4 := block052W4)
    (s1 := block052S1) (s2 := block052S2) (s3 := block052S3) (s4 := block052S4)
    hboxes hcover block052RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block052_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block052RightL : ℝ) (block052RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block052S1 : ℝ))
    (hy2ne : y ≠ (block052S2 : ℝ))
    (hy3ne : y ≠ (block052S3 : ℝ))
    (hy4ne : y ≠ (block052S4 : ℝ)) :
    0 < block052V y := by
  have hL : (block052RightChunk000L : ℝ) = (block052RightL : ℝ) := by
    norm_num [block052RightChunk000L, block052RightL]
  have hR : (block052RightChunk000R : ℝ) = (block052RightR : ℝ) := by
    norm_num [block052RightChunk000R, block052RightR]
  have hyc : y ∈ Icc (block052RightChunk000L : ℝ) (block052RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block052_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block052_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block052LeftL : ℝ) (block052LeftR : ℝ) →
    y ≠ 0 → y ≠ (block052S1 : ℝ) → y ≠ (block052S2 : ℝ) →
    y ≠ (block052S3 : ℝ) → y ≠ (block052S4 : ℝ) → 0 < block052V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block052RightL : ℝ) (block052RightR : ℝ) →
    y ≠ 0 → y ≠ (block052S1 : ℝ) → y ≠ (block052S2 : ℝ) →
    y ≠ (block052S3 : ℝ) → y ≠ (block052S4 : ℝ) → 0 < block052V y)

theorem block052_reallog_certificate_proof :
    block052_reallog_certificate := by
  exact ⟨block052_left_V_pos, block052_right_V_pos⟩

end Block052
end M1817475
end Erdos1038Lean
