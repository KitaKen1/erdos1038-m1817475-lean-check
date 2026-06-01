import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block363

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block363

open Set

def block363W1 : Rat := ((8807792774182291 : Rat) / 10000000000000000)
def block363W2 : Rat := ((11840020660607839 : Rat) / 250000000000000000)
def block363W3 : Rat := ((15266026736777283 : Rat) / 100000000000000000)
def block363W4 : Rat := ((13927109568961873 : Rat) / 100000000000000000)
def block363S1 : Rat := ((18174751 : Rat) / 10000000)
def block363S2 : Rat := ((511587 : Rat) / 200000)
def block363S3 : Rat := ((133037231339285714317 : Rat) / 50000000000000000000)
def block363S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block363V (y : ℝ) : ℝ :=
  ratPotential block363W1 block363W2 block363W3 block363W4 block363S1 block363S2 block363S3 block363S4 y

def block363LeftParamsCertificate : Bool :=
  allBoxesSameParams block363LeftBoxes block363W1 block363W2 block363W3 block363W4 block363S1 block363S2 block363S3 block363S4

theorem block363LeftParamsCertificate_eq_true :
    block363LeftParamsCertificate = true := by
  native_decide

theorem block363_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block363LeftL : ℝ) (block363LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block363S1 : ℝ))
    (hy2ne : y ≠ (block363S2 : ℝ))
    (hy3ne : y ≠ (block363S3 : ℝ))
    (hy4ne : y ≠ (block363S4 : ℝ)) :
    0 < block363V y := by
  have hcert := block363LeftCertificate_eq_true
  unfold block363LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block363LeftBoxes) (lo := block363LeftL) (hi := block363LeftR)
    (w1 := block363W1) (w2 := block363W2) (w3 := block363W3) (w4 := block363W4)
    (s1 := block363S1) (s2 := block363S2) (s3 := block363S3) (s4 := block363S4)
    hboxes hcover block363LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block363RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block363RightChunk000 block363W1 block363W2 block363W3 block363W4 block363S1 block363S2 block363S3 block363S4

theorem block363RightChunk000ParamsCertificate_eq_true :
    block363RightChunk000ParamsCertificate = true := by
  native_decide

theorem block363_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block363RightChunk000L : ℝ) (block363RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block363S1 : ℝ))
    (hy2ne : y ≠ (block363S2 : ℝ))
    (hy3ne : y ≠ (block363S3 : ℝ))
    (hy4ne : y ≠ (block363S4 : ℝ)) :
    0 < block363V y := by
  have hcert := block363RightChunk000Certificate_eq_true
  unfold block363RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block363RightChunk000) (lo := block363RightChunk000L) (hi := block363RightChunk000R)
    (w1 := block363W1) (w2 := block363W2) (w3 := block363W3) (w4 := block363W4)
    (s1 := block363S1) (s2 := block363S2) (s3 := block363S3) (s4 := block363S4)
    hboxes hcover block363RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block363_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block363RightL : ℝ) (block363RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block363S1 : ℝ))
    (hy2ne : y ≠ (block363S2 : ℝ))
    (hy3ne : y ≠ (block363S3 : ℝ))
    (hy4ne : y ≠ (block363S4 : ℝ)) :
    0 < block363V y := by
  have hL : (block363RightChunk000L : ℝ) = (block363RightL : ℝ) := by
    norm_num [block363RightChunk000L, block363RightL]
  have hR : (block363RightChunk000R : ℝ) = (block363RightR : ℝ) := by
    norm_num [block363RightChunk000R, block363RightR]
  have hyc : y ∈ Icc (block363RightChunk000L : ℝ) (block363RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block363_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block363_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block363LeftL : ℝ) (block363LeftR : ℝ) →
    y ≠ 0 → y ≠ (block363S1 : ℝ) → y ≠ (block363S2 : ℝ) →
    y ≠ (block363S3 : ℝ) → y ≠ (block363S4 : ℝ) → 0 < block363V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block363RightL : ℝ) (block363RightR : ℝ) →
    y ≠ 0 → y ≠ (block363S1 : ℝ) → y ≠ (block363S2 : ℝ) →
    y ≠ (block363S3 : ℝ) → y ≠ (block363S4 : ℝ) → 0 < block363V y)

theorem block363_reallog_certificate_proof :
    block363_reallog_certificate := by
  exact ⟨block363_left_V_pos, block363_right_V_pos⟩

end Block363
end M1817475
end Erdos1038Lean
