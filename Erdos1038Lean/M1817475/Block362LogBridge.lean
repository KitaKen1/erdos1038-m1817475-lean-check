import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block362

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block362

open Set

def block362W1 : Rat := ((2206438184832003 : Rat) / 2500000000000000)
def block362W2 : Rat := ((946850856029667 : Rat) / 20000000000000000)
def block362W3 : Rat := ((1525380232239707 : Rat) / 10000000000000000)
def block362W4 : Rat := ((6954144255196777 : Rat) / 50000000000000000)
def block362S1 : Rat := ((18174751 : Rat) / 10000000)
def block362S2 : Rat := ((511587 : Rat) / 200000)
def block362S3 : Rat := ((133056780446428571459 : Rat) / 50000000000000000000)
def block362S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block362V (y : ℝ) : ℝ :=
  ratPotential block362W1 block362W2 block362W3 block362W4 block362S1 block362S2 block362S3 block362S4 y

def block362LeftParamsCertificate : Bool :=
  allBoxesSameParams block362LeftBoxes block362W1 block362W2 block362W3 block362W4 block362S1 block362S2 block362S3 block362S4

theorem block362LeftParamsCertificate_eq_true :
    block362LeftParamsCertificate = true := by
  native_decide

theorem block362_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block362LeftL : ℝ) (block362LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block362S1 : ℝ))
    (hy2ne : y ≠ (block362S2 : ℝ))
    (hy3ne : y ≠ (block362S3 : ℝ))
    (hy4ne : y ≠ (block362S4 : ℝ)) :
    0 < block362V y := by
  have hcert := block362LeftCertificate_eq_true
  unfold block362LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block362LeftBoxes) (lo := block362LeftL) (hi := block362LeftR)
    (w1 := block362W1) (w2 := block362W2) (w3 := block362W3) (w4 := block362W4)
    (s1 := block362S1) (s2 := block362S2) (s3 := block362S3) (s4 := block362S4)
    hboxes hcover block362LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block362RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block362RightChunk000 block362W1 block362W2 block362W3 block362W4 block362S1 block362S2 block362S3 block362S4

theorem block362RightChunk000ParamsCertificate_eq_true :
    block362RightChunk000ParamsCertificate = true := by
  native_decide

theorem block362_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block362RightChunk000L : ℝ) (block362RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block362S1 : ℝ))
    (hy2ne : y ≠ (block362S2 : ℝ))
    (hy3ne : y ≠ (block362S3 : ℝ))
    (hy4ne : y ≠ (block362S4 : ℝ)) :
    0 < block362V y := by
  have hcert := block362RightChunk000Certificate_eq_true
  unfold block362RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block362RightChunk000) (lo := block362RightChunk000L) (hi := block362RightChunk000R)
    (w1 := block362W1) (w2 := block362W2) (w3 := block362W3) (w4 := block362W4)
    (s1 := block362S1) (s2 := block362S2) (s3 := block362S3) (s4 := block362S4)
    hboxes hcover block362RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block362_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block362RightL : ℝ) (block362RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block362S1 : ℝ))
    (hy2ne : y ≠ (block362S2 : ℝ))
    (hy3ne : y ≠ (block362S3 : ℝ))
    (hy4ne : y ≠ (block362S4 : ℝ)) :
    0 < block362V y := by
  have hL : (block362RightChunk000L : ℝ) = (block362RightL : ℝ) := by
    norm_num [block362RightChunk000L, block362RightL]
  have hR : (block362RightChunk000R : ℝ) = (block362RightR : ℝ) := by
    norm_num [block362RightChunk000R, block362RightR]
  have hyc : y ∈ Icc (block362RightChunk000L : ℝ) (block362RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block362_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block362_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block362LeftL : ℝ) (block362LeftR : ℝ) →
    y ≠ 0 → y ≠ (block362S1 : ℝ) → y ≠ (block362S2 : ℝ) →
    y ≠ (block362S3 : ℝ) → y ≠ (block362S4 : ℝ) → 0 < block362V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block362RightL : ℝ) (block362RightR : ℝ) →
    y ≠ 0 → y ≠ (block362S1 : ℝ) → y ≠ (block362S2 : ℝ) →
    y ≠ (block362S3 : ℝ) → y ≠ (block362S4 : ℝ) → 0 < block362V y)

theorem block362_reallog_certificate_proof :
    block362_reallog_certificate := by
  exact ⟨block362_left_V_pos, block362_right_V_pos⟩

end Block362
end M1817475
end Erdos1038Lean
