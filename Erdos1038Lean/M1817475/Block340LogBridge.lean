import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block340

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block340

open Set

def block340W1 : Rat := ((2317912749508087 : Rat) / 2500000000000000)
def block340W2 : Rat := ((23740724542305587 : Rat) / 500000000000000000)
def block340W3 : Rat := ((730853464834767 : Rat) / 5000000000000000)
def block340W4 : Rat := ((6874268175946681 : Rat) / 50000000000000000)
def block340S1 : Rat := ((18174751 : Rat) / 10000000)
def block340S2 : Rat := ((511587 : Rat) / 200000)
def block340S3 : Rat := ((133486860803571428583 : Rat) / 50000000000000000000)
def block340S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block340V (y : ℝ) : ℝ :=
  ratPotential block340W1 block340W2 block340W3 block340W4 block340S1 block340S2 block340S3 block340S4 y

def block340LeftParamsCertificate : Bool :=
  allBoxesSameParams block340LeftBoxes block340W1 block340W2 block340W3 block340W4 block340S1 block340S2 block340S3 block340S4

theorem block340LeftParamsCertificate_eq_true :
    block340LeftParamsCertificate = true := by
  native_decide

theorem block340_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block340LeftL : ℝ) (block340LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block340S1 : ℝ))
    (hy2ne : y ≠ (block340S2 : ℝ))
    (hy3ne : y ≠ (block340S3 : ℝ))
    (hy4ne : y ≠ (block340S4 : ℝ)) :
    0 < block340V y := by
  have hcert := block340LeftCertificate_eq_true
  unfold block340LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block340LeftBoxes) (lo := block340LeftL) (hi := block340LeftR)
    (w1 := block340W1) (w2 := block340W2) (w3 := block340W3) (w4 := block340W4)
    (s1 := block340S1) (s2 := block340S2) (s3 := block340S3) (s4 := block340S4)
    hboxes hcover block340LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block340RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block340RightChunk000 block340W1 block340W2 block340W3 block340W4 block340S1 block340S2 block340S3 block340S4

theorem block340RightChunk000ParamsCertificate_eq_true :
    block340RightChunk000ParamsCertificate = true := by
  native_decide

theorem block340_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block340RightChunk000L : ℝ) (block340RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block340S1 : ℝ))
    (hy2ne : y ≠ (block340S2 : ℝ))
    (hy3ne : y ≠ (block340S3 : ℝ))
    (hy4ne : y ≠ (block340S4 : ℝ)) :
    0 < block340V y := by
  have hcert := block340RightChunk000Certificate_eq_true
  unfold block340RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block340RightChunk000) (lo := block340RightChunk000L) (hi := block340RightChunk000R)
    (w1 := block340W1) (w2 := block340W2) (w3 := block340W3) (w4 := block340W4)
    (s1 := block340S1) (s2 := block340S2) (s3 := block340S3) (s4 := block340S4)
    hboxes hcover block340RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block340_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block340RightL : ℝ) (block340RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block340S1 : ℝ))
    (hy2ne : y ≠ (block340S2 : ℝ))
    (hy3ne : y ≠ (block340S3 : ℝ))
    (hy4ne : y ≠ (block340S4 : ℝ)) :
    0 < block340V y := by
  have hL : (block340RightChunk000L : ℝ) = (block340RightL : ℝ) := by
    norm_num [block340RightChunk000L, block340RightL]
  have hR : (block340RightChunk000R : ℝ) = (block340RightR : ℝ) := by
    norm_num [block340RightChunk000R, block340RightR]
  have hyc : y ∈ Icc (block340RightChunk000L : ℝ) (block340RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block340_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block340_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block340LeftL : ℝ) (block340LeftR : ℝ) →
    y ≠ 0 → y ≠ (block340S1 : ℝ) → y ≠ (block340S2 : ℝ) →
    y ≠ (block340S3 : ℝ) → y ≠ (block340S4 : ℝ) → 0 < block340V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block340RightL : ℝ) (block340RightR : ℝ) →
    y ≠ 0 → y ≠ (block340S1 : ℝ) → y ≠ (block340S2 : ℝ) →
    y ≠ (block340S3 : ℝ) → y ≠ (block340S4 : ℝ) → 0 < block340V y)

theorem block340_reallog_certificate_proof :
    block340_reallog_certificate := by
  exact ⟨block340_left_V_pos, block340_right_V_pos⟩

end Block340
end M1817475
end Erdos1038Lean
