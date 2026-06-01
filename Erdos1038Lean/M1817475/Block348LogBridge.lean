import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block348

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block348

open Set

def block348W1 : Rat := ((9107112072227497 : Rat) / 10000000000000000)
def block348W2 : Rat := ((11877830935827241 : Rat) / 250000000000000000)
def block348W3 : Rat := ((1482747348021269 : Rat) / 10000000000000000)
def block348W4 : Rat := ((1727457562015177 : Rat) / 12500000000000000)
def block348S1 : Rat := ((18174751 : Rat) / 10000000)
def block348S2 : Rat := ((511587 : Rat) / 200000)
def block348S3 : Rat := ((133330467946428571447 : Rat) / 50000000000000000000)
def block348S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block348V (y : ℝ) : ℝ :=
  ratPotential block348W1 block348W2 block348W3 block348W4 block348S1 block348S2 block348S3 block348S4 y

def block348LeftParamsCertificate : Bool :=
  allBoxesSameParams block348LeftBoxes block348W1 block348W2 block348W3 block348W4 block348S1 block348S2 block348S3 block348S4

theorem block348LeftParamsCertificate_eq_true :
    block348LeftParamsCertificate = true := by
  native_decide

theorem block348_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block348LeftL : ℝ) (block348LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block348S1 : ℝ))
    (hy2ne : y ≠ (block348S2 : ℝ))
    (hy3ne : y ≠ (block348S3 : ℝ))
    (hy4ne : y ≠ (block348S4 : ℝ)) :
    0 < block348V y := by
  have hcert := block348LeftCertificate_eq_true
  unfold block348LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block348LeftBoxes) (lo := block348LeftL) (hi := block348LeftR)
    (w1 := block348W1) (w2 := block348W2) (w3 := block348W3) (w4 := block348W4)
    (s1 := block348S1) (s2 := block348S2) (s3 := block348S3) (s4 := block348S4)
    hboxes hcover block348LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block348RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block348RightChunk000 block348W1 block348W2 block348W3 block348W4 block348S1 block348S2 block348S3 block348S4

theorem block348RightChunk000ParamsCertificate_eq_true :
    block348RightChunk000ParamsCertificate = true := by
  native_decide

theorem block348_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block348RightChunk000L : ℝ) (block348RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block348S1 : ℝ))
    (hy2ne : y ≠ (block348S2 : ℝ))
    (hy3ne : y ≠ (block348S3 : ℝ))
    (hy4ne : y ≠ (block348S4 : ℝ)) :
    0 < block348V y := by
  have hcert := block348RightChunk000Certificate_eq_true
  unfold block348RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block348RightChunk000) (lo := block348RightChunk000L) (hi := block348RightChunk000R)
    (w1 := block348W1) (w2 := block348W2) (w3 := block348W3) (w4 := block348W4)
    (s1 := block348S1) (s2 := block348S2) (s3 := block348S3) (s4 := block348S4)
    hboxes hcover block348RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block348_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block348RightL : ℝ) (block348RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block348S1 : ℝ))
    (hy2ne : y ≠ (block348S2 : ℝ))
    (hy3ne : y ≠ (block348S3 : ℝ))
    (hy4ne : y ≠ (block348S4 : ℝ)) :
    0 < block348V y := by
  have hL : (block348RightChunk000L : ℝ) = (block348RightL : ℝ) := by
    norm_num [block348RightChunk000L, block348RightL]
  have hR : (block348RightChunk000R : ℝ) = (block348RightR : ℝ) := by
    norm_num [block348RightChunk000R, block348RightR]
  have hyc : y ∈ Icc (block348RightChunk000L : ℝ) (block348RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block348_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block348_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block348LeftL : ℝ) (block348LeftR : ℝ) →
    y ≠ 0 → y ≠ (block348S1 : ℝ) → y ≠ (block348S2 : ℝ) →
    y ≠ (block348S3 : ℝ) → y ≠ (block348S4 : ℝ) → 0 < block348V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block348RightL : ℝ) (block348RightR : ℝ) →
    y ≠ 0 → y ≠ (block348S1 : ℝ) → y ≠ (block348S2 : ℝ) →
    y ≠ (block348S3 : ℝ) → y ≠ (block348S4 : ℝ) → 0 < block348V y)

theorem block348_reallog_certificate_proof :
    block348_reallog_certificate := by
  exact ⟨block348_left_V_pos, block348_right_V_pos⟩

end Block348
end M1817475
end Erdos1038Lean
