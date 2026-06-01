import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block335

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block335

open Set

def block335W1 : Rat := ((9386554495149547 : Rat) / 10000000000000000)
def block335W2 : Rat := ((2365544121424913 : Rat) / 50000000000000000)
def block335W3 : Rat := ((1808451117390093 : Rat) / 12500000000000000)
def block335W4 : Rat := ((1372360314347817 : Rat) / 10000000000000000)
def block335S1 : Rat := ((18174751 : Rat) / 10000000)
def block335S2 : Rat := ((511587 : Rat) / 200000)
def block335S3 : Rat := ((133584606339285714293 : Rat) / 50000000000000000000)
def block335S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block335V (y : ℝ) : ℝ :=
  ratPotential block335W1 block335W2 block335W3 block335W4 block335S1 block335S2 block335S3 block335S4 y

def block335LeftParamsCertificate : Bool :=
  allBoxesSameParams block335LeftBoxes block335W1 block335W2 block335W3 block335W4 block335S1 block335S2 block335S3 block335S4

theorem block335LeftParamsCertificate_eq_true :
    block335LeftParamsCertificate = true := by
  native_decide

theorem block335_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block335LeftL : ℝ) (block335LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block335S1 : ℝ))
    (hy2ne : y ≠ (block335S2 : ℝ))
    (hy3ne : y ≠ (block335S3 : ℝ))
    (hy4ne : y ≠ (block335S4 : ℝ)) :
    0 < block335V y := by
  have hcert := block335LeftCertificate_eq_true
  unfold block335LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block335LeftBoxes) (lo := block335LeftL) (hi := block335LeftR)
    (w1 := block335W1) (w2 := block335W2) (w3 := block335W3) (w4 := block335W4)
    (s1 := block335S1) (s2 := block335S2) (s3 := block335S3) (s4 := block335S4)
    hboxes hcover block335LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block335RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block335RightChunk000 block335W1 block335W2 block335W3 block335W4 block335S1 block335S2 block335S3 block335S4

theorem block335RightChunk000ParamsCertificate_eq_true :
    block335RightChunk000ParamsCertificate = true := by
  native_decide

theorem block335_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block335RightChunk000L : ℝ) (block335RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block335S1 : ℝ))
    (hy2ne : y ≠ (block335S2 : ℝ))
    (hy3ne : y ≠ (block335S3 : ℝ))
    (hy4ne : y ≠ (block335S4 : ℝ)) :
    0 < block335V y := by
  have hcert := block335RightChunk000Certificate_eq_true
  unfold block335RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block335RightChunk000) (lo := block335RightChunk000L) (hi := block335RightChunk000R)
    (w1 := block335W1) (w2 := block335W2) (w3 := block335W3) (w4 := block335W4)
    (s1 := block335S1) (s2 := block335S2) (s3 := block335S3) (s4 := block335S4)
    hboxes hcover block335RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block335_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block335RightL : ℝ) (block335RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block335S1 : ℝ))
    (hy2ne : y ≠ (block335S2 : ℝ))
    (hy3ne : y ≠ (block335S3 : ℝ))
    (hy4ne : y ≠ (block335S4 : ℝ)) :
    0 < block335V y := by
  have hL : (block335RightChunk000L : ℝ) = (block335RightL : ℝ) := by
    norm_num [block335RightChunk000L, block335RightL]
  have hR : (block335RightChunk000R : ℝ) = (block335RightR : ℝ) := by
    norm_num [block335RightChunk000R, block335RightR]
  have hyc : y ∈ Icc (block335RightChunk000L : ℝ) (block335RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block335_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block335_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block335LeftL : ℝ) (block335LeftR : ℝ) →
    y ≠ 0 → y ≠ (block335S1 : ℝ) → y ≠ (block335S2 : ℝ) →
    y ≠ (block335S3 : ℝ) → y ≠ (block335S4 : ℝ) → 0 < block335V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block335RightL : ℝ) (block335RightR : ℝ) →
    y ≠ 0 → y ≠ (block335S1 : ℝ) → y ≠ (block335S2 : ℝ) →
    y ≠ (block335S3 : ℝ) → y ≠ (block335S4 : ℝ) → 0 < block335V y)

theorem block335_reallog_certificate_proof :
    block335_reallog_certificate := by
  exact ⟨block335_left_V_pos, block335_right_V_pos⟩

end Block335
end M1817475
end Erdos1038Lean
